from collections import OrderedDict
from p4z3.base import log, DefaultExpression, copy, z3_cast, merge_attrs, z3
from p4z3.base import StructInstance, P4Statement, P4Z3Class, gen_instance
from p4z3.base import ParserException, P4Mask, P4Range
from p4z3.parser import RejectState


class AssignmentStatement(P4Statement):
    # AssignmentStatements are essentially just a wrapper class for the
    # set_or_add_var ḿethod of the p4 state.
    # All the important logic is handled there.

    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_state):
        log.debug("Assigning %s to %s ", self.rval, self.lval)
        rval_expr = p4_state.resolve_expr(self.rval)
        # in assignments all complex types values are copied
        if isinstance(rval_expr, StructInstance):
            rval_expr = copy.copy(rval_expr)
        if isinstance(rval_expr, int):
            lval = p4_state.resolve_expr(self.lval)
            rval_expr = z3_cast(rval_expr, lval.sort())
        p4_state.set_or_add_var(self.lval, rval_expr)


class MethodCallStmt(P4Statement):

    def __init__(self, method_expr):
        self.method_expr = method_expr

    def eval(self, p4_state):
        self.method_expr.eval(p4_state)


class BlockStatement(P4Statement):

    def __init__(self, exprs):
        self.exprs = exprs

    def eval(self, p4_state):
        for expr in self.exprs:
            expr.eval(p4_state)
            if p4_state.has_exited or p4_state.current_context().has_returned:
                break


class IfStatement(P4Statement):

    def __init__(self, cond, then_block, else_block=None):
        self.cond = cond
        self.then_block = then_block
        if not else_block:
            self.else_block = P4Noop()
        else:
            self.else_block = else_block

    def eval(self, p4_state):
        context = p4_state.current_context()
        cond = z3.simplify(p4_state.resolve_expr(self.cond))
        forward_cond_copy = context.tmp_forward_cond
        then_vars = None
        if not cond == z3.BoolVal(False):
            var_store, contexts = p4_state.checkpoint()
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            try:
                self.then_block.eval(p4_state)
            except ParserException:
                RejectState().eval(p4_state)
            if not(context.has_returned or p4_state.has_exited):
                then_vars = p4_state.get_attrs()
            p4_state.has_exited = False
            context.has_returned = False
            p4_state.restore(var_store, contexts)

        if not cond == z3.BoolVal(True):
            var_store, contexts = p4_state.checkpoint()
            context.tmp_forward_cond = z3.And(forward_cond_copy, z3.Not(cond))
            try:
                self.else_block.eval(p4_state)
            except ParserException:
                RejectState().eval(p4_state)
            if p4_state.has_exited or context.has_returned:
                p4_state.restore(var_store, contexts)
            p4_state.has_exited = False
            context.has_returned = False

        context.tmp_forward_cond = forward_cond_copy

        if then_vars:
            merge_attrs(p4_state, cond, then_vars)


class SwitchHit(P4Z3Class):
    def __init__(self, cases, default_case):
        self.default_case = default_case
        self.cases = cases
        self.table = None

    def eval_cases(self, p4_state, cases):
        case_exprs = []
        case_matches = []
        context = p4_state.current_context()
        forward_cond_copy = context.tmp_forward_cond
        fall_through_matches = []
        for case in cases.values():
            match = case["match"]
            if not case["case_block"]:
                fall_through_matches.append(match)
                continue
            match = z3.Or(match, *fall_through_matches)
            var_store, contexts = p4_state.checkpoint()
            context.tmp_forward_cond = z3.And(
                forward_cond_copy, match)
            case["case_block"].eval(p4_state)
            fall_through_matches.clear()
            if not (context.has_returned or p4_state.has_exited):
                then_vars = p4_state.get_attrs()
                case_exprs.append((match, then_vars))
            context.has_returned = False
            p4_state.has_exited = False
            p4_state.restore(var_store, contexts)
            case_matches.append(match)
        var_store, contexts = p4_state.checkpoint()
        cond = z3.Not(z3.Or(*case_matches))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        self.default_case.eval(p4_state)
        if context.has_returned or p4_state.has_exited:
            p4_state.restore(var_store, contexts)
        context.has_returned = False
        p4_state.has_exited = False
        context.tmp_forward_cond = forward_cond_copy
        for cond, then_vars in reversed(case_exprs):
            merge_attrs(p4_state, cond, then_vars)

    def set_table(self, table):
        self.table = table

    def eval_switch_matches(self, p4_state, table):
        if table.immutable:
            for c_keys, (action_name, _) in table.const_entries:
                const_matches = []
                if action_name not in self.cases:
                    continue
                matches = []
                # match the constant keys with the normal table keys
                # this generates the match expression for a specific constant entry
                # this is a little inefficient, fix.
                # TODO: Figure out if key type matters here?
                for index, (key_expr, _) in enumerate(table.keys):
                    c_key_expr = c_keys[index]
                    # default implies don't care, do not add
                    # TODO: Verify that this assumption is right...
                    if isinstance(c_key_expr, DefaultExpression):
                        continue
                    key_eval = p4_state.resolve_expr(key_expr)
                    if isinstance(c_key_expr, P4Range):
                        x = c_key_expr.min
                        y = c_key_expr.max
                        c_key_eval = z3.And(z3.ULE(x, key_eval),
                                            z3.UGE(y, key_eval))
                        matches.append(c_key_eval)
                    elif isinstance(c_key_expr, P4Mask):
                        val = p4_state.resolve_expr(c_key_expr.mask)
                        mask = c_key_expr.mask
                        c_key_eval = (val & mask) == (key_eval & mask)
                        matches.append(c_key_eval)
                    else:
                        c_key_eval = p4_state.resolve_expr(c_key_expr)
                        matches.append(key_eval == c_key_eval)
                action = table.actions[action_name][0]
                match_expr = z3.And(*matches)
                if "match" in self.cases[action_name]:
                    prev_match = self.cases[action_name]["match"]
                    match_expr = z3.Or(match_expr, prev_match)
                const_matches.append(match_expr)
                self.cases[action_name]["match"] = match_expr
            _, action_name, action_args = table.default_action
            match_expr = z3.Not(z3.Or(*const_matches))
            if "match" in self.cases[action_name]:
                prev_match = self.cases[action_name]["match"]
                match_expr = z3.Or(match_expr, prev_match)
            const_matches.append(match_expr)
            self.cases[action_name]["match"] = match_expr
        else:
            for case_name, case in self.cases.items():
                match_var = table.tbl_action
                action = table.actions[case_name][0]
                match_cond = z3.And(table.locals["hit"], (action == match_var))
                self.cases[case_name]["match"] = match_cond

    def eval(self, p4_state):
        self.eval_switch_matches(p4_state, self.table)
        self.eval_cases(p4_state, self.cases)


class SwitchStatement(P4Statement):
    def __init__(self, switch_expr, cases):
        self.switch_expr = switch_expr
        self.default_case = P4Noop()
        self.cases = OrderedDict()
        for action_str, case_stmt in cases:
            self.add_case(action_str)
            if case_stmt is not None:
                # TODO: Check if this models fall-through correctly
                self.add_stmt_to_case(action_str, case_stmt)

    def add_case(self, action_str):
        # skip default statements, they are handled separately
        if isinstance(action_str, DefaultExpression):
            return
        case = {}
        case["case_block"] = None
        self.cases[action_str] = case

    def add_stmt_to_case(self, action_str, case_stmt):
        if isinstance(action_str, DefaultExpression):
            self.default_case = case_stmt
        else:
            if not self.cases[action_str]["case_block"]:
                self.cases[action_str]["case_block"] = BlockStatement([])
            self.cases[action_str]["case_block"] = case_stmt

    def eval_cases(self, p4_state, switch_expr, cases):
        case_exprs = []
        case_matches = []
        context = p4_state.current_context()
        forward_cond_copy = context.tmp_forward_cond
        fall_through_matches = []
        for case_val, case in cases.items():
            # assume the value has no side-effects
            case_val = p4_state.resolve_expr(case_val)
            match = switch_expr == case_val
            var_store, contexts = p4_state.checkpoint()
            context.tmp_forward_cond = z3.And(
                forward_cond_copy, match)
            if not case["case_block"]:
                fall_through_matches.append(match)
                continue
            case["case_block"].eval(p4_state)
            match = z3.Or(match, *fall_through_matches)
            fall_through_matches.clear()
            if not (context.has_returned or p4_state.has_exited):
                then_vars = p4_state.get_attrs()
                case_exprs.append((match, then_vars))
            context.has_returned = False
            p4_state.has_exited = False
            p4_state.restore(var_store, contexts)
            case_matches.append(match)
        var_store, contexts = p4_state.checkpoint()
        cond = z3.Not(z3.Or(*case_matches))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        self.default_case.eval(p4_state)
        if context.has_returned or p4_state.has_exited:
            p4_state.restore(var_store, contexts)
        context.has_returned = False
        p4_state.has_exited = False
        context.tmp_forward_cond = forward_cond_copy
        for cond, then_vars in reversed(case_exprs):
            merge_attrs(p4_state, cond, then_vars)

    def eval(self, p4_state):
        switch_expr = p4_state.resolve_expr(self.switch_expr)
        if isinstance(switch_expr, z3.ExprRef):
            self.eval_cases(p4_state, switch_expr, self.cases)
        else:
            table = self.switch_expr.eval(p4_state)
            switch_hit = SwitchHit(self.cases, self.default_case)
            switch_hit.set_table(table)
            switch_hit.eval(p4_state)


class P4Noop(P4Statement):

    def eval(self, p4_state):
        pass


class P4Return(P4Statement):
    def __init__(self, expr=None):
        self.expr = expr

    def eval(self, p4_state):
        context = p4_state.current_context()

        if self.expr is None:
            expr = None
        else:
            # resolve the expr before restoring the state
            expr = p4_state.resolve_expr(self.expr)
            if isinstance(context.return_type, z3.BitVecSortRef):
                expr = z3_cast(expr, context.return_type)
            # we return a complex typed expression list, instantiate
            if isinstance(expr, list):
                instance = gen_instance(p4_state, "undefined",
                                        context.return_type)
                instance.set_list(expr)
                expr = instance

        cond = z3.simplify(z3.And(z3.Not(z3.Or(*context.forward_conds)),
                                  context.tmp_forward_cond))
        if not cond == z3.BoolVal(False):
            context.return_states.append((cond, p4_state.copy_attrs()))
            if expr is not None:
                context.return_exprs.append((cond, expr))
            context.has_returned = True
        context.forward_conds.append(context.tmp_forward_cond)


class P4Exit(P4Statement):

    def eval(self, p4_state):
        # FIXME: This checkpointing should not be necessary
        # Figure out what is going on
        var_store, contexts = p4_state.checkpoint()
        forward_conds = []
        tmp_forward_conds = []
        for context in reversed(p4_state.contexts):
            context.copy_out(p4_state)
            forward_conds.extend(context.forward_conds)
            tmp_forward_conds.append(context.tmp_forward_cond)
        context = p4_state.current_context()

        cond = z3.simplify(z3.And(z3.Not(z3.Or(*forward_conds)),
                                  z3.And(*tmp_forward_conds)))
        if not cond == z3.BoolVal(False):
            p4_state.exit_states.append((cond, p4_state.get_members()))
            p4_state.has_exited = True
        p4_state.restore(var_store, contexts)
        context.forward_conds.append(context.tmp_forward_cond)
