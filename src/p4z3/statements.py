from collections import OrderedDict
from p4z3.base import log, DefaultExpression, copy, z3_cast, merge_attrs, z3
from p4z3.base import StructInstance, P4Statement, gen_instance
from p4z3.base import ParserException
from p4z3.callables import P4Table
from p4z3.parser import RejectState
from p4z3.state import StaticContext


class AssignmentStatement(P4Statement):
    # AssignmentStatements are essentially just a wrapper class for the
    # set_or_add_var ḿethod of the p4 state.
    # All the important logic is handled there.

    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, context):
        log.debug("Assigning %s to %s ", self.rval, self.lval)
        rval_expr = context.resolve_expr(self.rval)
        # in assignments all complex types values are copied
        if isinstance(rval_expr, StructInstance):
            rval_expr = copy.copy(rval_expr)
        if isinstance(rval_expr, int):
            lval = context.resolve_expr(self.lval)
            rval_expr = z3_cast(rval_expr, lval.sort())
        context.set_or_add_var(self.lval, rval_expr)


class MethodCallStmt(P4Statement):

    def __init__(self, method_expr):
        self.method_expr = method_expr

    def eval(self, context):
        self.method_expr.eval(context)


class BlockStatement(P4Statement):

    def __init__(self, exprs):
        self.exprs = exprs

    def eval(self, context):
        for expr in self.exprs:
            expr.eval(context)
            if context.get_exited() or context.has_returned:
                break


class IfStatement(P4Statement):

    def __init__(self, cond, then_block, else_block=None):
        self.cond = cond
        self.then_block = then_block
        if not else_block:
            self.else_block = P4Noop()
        else:
            self.else_block = else_block

    def eval(self, context):
        cond = z3.simplify(context.resolve_expr(self.cond))
        forward_cond_copy = context.tmp_forward_cond
        then_vars = None
        if not z3.is_false(cond):
            var_store, contexts = context.checkpoint()
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            try:
                self.then_block.eval(context)
            except ParserException:
                RejectState().eval(context)
            if not(context.has_returned or context.get_exited()):
                then_vars = context.get_attrs()
            context.set_exited(False)
            context.has_returned = False
            context.restore(var_store, contexts)

        if not z3.is_true(cond):
            var_store, contexts = context.checkpoint()
            context.tmp_forward_cond = z3.And(forward_cond_copy, z3.Not(cond))
            try:
                self.else_block.eval(context)
            except ParserException:
                RejectState().eval(context)
            if context.get_exited() or context.has_returned:
                context.restore(var_store, contexts)
            context.set_exited(False)
            context.has_returned = False

        context.tmp_forward_cond = forward_cond_copy

        if then_vars:
            merge_attrs(context, cond, then_vars)


class SwitchStatement(P4Statement):
    def __init__(self, switch_expr, cases):
        self.switch_expr = switch_expr
        self.default_case = P4Noop()
        self.case_blocks = OrderedDict()
        for action_str, case_stmt in cases:
            self.add_stmt_to_case(action_str, case_stmt)

    def add_stmt_to_case(self, action_str, case_stmt):
        # default statements are handled separately
        if isinstance(action_str, DefaultExpression):
            self.default_case = case_stmt
            return
        self.case_blocks[action_str] = case_stmt

    def eval_cases(self, context, cases):
        case_exprs = []
        case_matches = []
        forward_cond_copy = context.tmp_forward_cond
        fall_through_matches = []
        for case_match, case_block in cases.values():
            # there is no block for the switch
            # this expressions falls through to the next switch case
            if not case_block:
                fall_through_matches.append(case_match)
                continue
            # matches the condition OR all the other fall-through switches
            case_match = z3.Or(case_match, *fall_through_matches)
            fall_through_matches.clear()
            var_store, contexts = context.checkpoint()
            context.tmp_forward_cond = z3.And(
                forward_cond_copy, case_match)
            case_block.eval(context)
            if not (context.has_returned or context.get_exited()):
                then_vars = context.get_attrs()
                case_exprs.append((case_match, then_vars))
            context.has_returned = False
            context.set_exited(False)
            context.restore(var_store, contexts)
            case_matches.append(case_match)
        var_store, contexts = context.checkpoint()
        # process the default expression
        cond = z3.Not(z3.Or(*case_matches))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        self.default_case.eval(context)
        if context.has_returned or context.get_exited():
            context.restore(var_store, contexts)
        context.has_returned = False
        context.set_exited(False)
        context.tmp_forward_cond = forward_cond_copy
        # merge all the expressions in reverse order
        for cond, then_vars in reversed(case_exprs):
            merge_attrs(context, cond, then_vars)

    def eval_switch_table_matches(self, context, table):
        cases = {}
        if table.immutable:
            # if the table is immutable we can only match on const entries
            for c_keys, (action_name, _) in table.const_entries:
                const_matches = []
                # check if the action of the entry is even present
                if action_name not in self.case_blocks:
                    continue
                # compute the match key
                # FIXME: Deal with side effects here
                # Maybe just checkpoint and restore? Ugh. So expensive...
                match_cond = table.get_const_matches(context, c_keys)
                action = table.actions[action_name][0]
                if action_name in cases:
                    prev_match, _ = cases[action_name]
                    match_cond = z3.Or(match_cond, prev_match)
                const_matches.append(match_cond)
                cases[action_name] = (
                    match_cond, self.case_blocks[action_name])

            # we also need to process the default action separately
            # this basically hits only if no other case matches
            _, action_name, _ = table.default_action
            match_cond = z3.Not(z3.Or(*const_matches))
            if action_name in cases:
                prev_match, _ = cases[action_name]
                match_cond = z3.Or(match_cond, prev_match)
            const_matches.append(match_cond)
            cases[action_name] = (match_cond, self.case_blocks[action_name])
        else:
            # otherwise we are dealing with a normal table
            # just insert the match entries combined with the hit expression
            for case_name, case_block in self.case_blocks.items():
                match_var = table.tbl_action
                action = table.actions[case_name][0]
                match_cond = z3.And(table.locals["hit"], (action == match_var))
                cases[case_name] = (match_cond, case_block)
        return cases

    def eval_switch_expr_matches(self, context, switch_expr):
        cases = {}
        for case_val, case_block in self.case_blocks.items():
            # assume the value has no side-effects
            case_val = context.resolve_expr(case_val)
            match_cond = switch_expr == case_val
            cases[case_val] = (match_cond, case_block)
        return cases

    def eval(self, context):
        switch_expr = context.resolve_expr(self.switch_expr)
        if isinstance(switch_expr, P4Table):
            # check whether we are dealing with a table switch case
            cases = self.eval_switch_table_matches(context, table=switch_expr)
        else:
            # or just a general switch case on an expression
            cases = self.eval_switch_expr_matches(context, switch_expr)
        self.eval_cases(context, cases)


class P4Noop(P4Statement):

    def eval(self, context):
        pass


class P4Return(P4Statement):
    def __init__(self, expr=None):
        self.expr = expr

    def eval(self, context):

        if self.expr is None:
            expr = None
        else:
            # resolve the expr before restoring the state
            expr = context.resolve_expr(self.expr)
            if isinstance(context.return_type, z3.BitVecSortRef):
                expr = z3_cast(expr, context.return_type)
            # we return a complex typed expression list, instantiate
            if isinstance(expr, list):
                # name is meaningless here so keep it empty
                instance = gen_instance(context, "", context.return_type)
                instance.set_list(expr)
                expr = instance

        cond = z3.simplify(z3.And(z3.Not(z3.Or(*context.forward_conds)),
                                  context.tmp_forward_cond))
        if not z3.is_false(cond):
            context.return_states.append((cond, context.copy_attrs()))
            if expr is not None:
                context.return_exprs.append((cond, expr))
            context.has_returned = True
        context.forward_conds.append(context.tmp_forward_cond)


class P4Exit(P4Statement):

    def eval(self, context):
        # FIXME: This checkpointing should not be necessary
        # Figure out what is going on
        var_store, contexts = context.checkpoint()
        forward_conds = []
        tmp_forward_conds = []
        sub_ctx = context
        while not isinstance(sub_ctx, StaticContext):
            sub_ctx.copy_out(context)
            forward_conds.extend(sub_ctx.forward_conds)
            tmp_forward_conds.append(sub_ctx.tmp_forward_cond)
            sub_ctx = sub_ctx.parent_context

        cond = z3.simplify(z3.And(z3.Not(z3.Or(*forward_conds)),
                                  z3.And(*tmp_forward_conds)))
        if not z3.is_false(cond):
            context.add_exit_state(
                cond, context.get_p4_state().get_members(context))
            context.set_exited(True)
        context.restore(var_store, contexts)
        context.forward_conds.append(context.tmp_forward_cond)
