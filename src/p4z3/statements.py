from collections import OrderedDict
from p4z3.base import log, DefaultExpression, copy, z3_cast, merge_attrs, z3
from p4z3.base import StructInstance, P4Statement, ParserException
from p4z3.callables import P4Table, resolve_index
from p4z3.parser import RejectState
from p4z3.state import StaticContext


class AssignmentStatement(P4Statement):
    # AssignmentStatements are essentially just a wrapper class for the
    # set_or_add_var ḿethod of the p4 state.
    # All the important logic is handled there.

    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, ctx):
        # An assignment, written with the = sign, first evaluates its left
        # sub-expression to an l-value, then evaluates its right sub-expression
        # to a value, and finally copies the value into the l-value. Derived
        # types (e.g. structs) are copied recursively, and all components of
        # headers are copied, including “validity” bits. Assignment is not
        # defined for extern values.
        log.debug("Assigning %s to %s ", self.rval, self.lval)
        lval, _ = resolve_index(ctx, self.lval)
        rval_expr = ctx.resolve_expr(self.rval)
        # in assignments all complex types values are copied
        if isinstance(rval_expr, StructInstance):
            rval_expr = copy.copy(rval_expr)
        if isinstance(rval_expr, int):
            rval_expr = z3_cast(rval_expr, ctx.resolve_expr(self.lval).sort())
        ctx.set_or_add_var(lval, rval_expr)


class MethodCallStmt(P4Statement):

    def __init__(self, method_expr):
        self.method_expr = method_expr

    def eval(self, ctx):
        self.method_expr.eval(ctx)


class BlockStatement(P4Statement):

    def __init__(self, exprs):
        self.exprs = exprs

    def eval(self, ctx):
        for expr in self.exprs:
            expr.eval(ctx)
            if ctx.get_exited() or ctx.has_returned:
                break


class IfStatement(P4Statement):

    def __init__(self, cond, then_block, else_block=None):
        self.cond = cond
        self.then_block = then_block
        if not else_block:
            self.else_block = P4Noop()
        else:
            self.else_block = else_block

    def eval(self, ctx):
        cond = z3.simplify(ctx.resolve_expr(self.cond))
        forward_cond_copy = ctx.tmp_forward_cond
        then_vars = None
        if not z3.is_false(cond):
            var_store = ctx.checkpoint()
            ctx.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            try:
                self.then_block.eval(ctx)
            except ParserException:
                RejectState().eval(ctx)
            if not(ctx.has_returned or ctx.get_exited()):
                then_vars = ctx.get_attrs()
            ctx.set_exited(False)
            ctx.has_returned = False
            ctx.restore(var_store)

        if not z3.is_true(cond):
            var_store = ctx.checkpoint()
            ctx.tmp_forward_cond = z3.And(forward_cond_copy, z3.Not(cond))
            try:
                self.else_block.eval(ctx)
            except ParserException:
                RejectState().eval(ctx)
            if ctx.get_exited() or ctx.has_returned:
                ctx.restore(var_store)
            ctx.set_exited(False)
            ctx.has_returned = False

        ctx.tmp_forward_cond = forward_cond_copy

        if then_vars:
            merge_attrs(ctx, cond, then_vars)


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

    def eval_cases(self, ctx, cases):
        case_exprs = []
        case_matches = []
        forward_cond_copy = ctx.tmp_forward_cond
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
            var_store = ctx.checkpoint()
            ctx.tmp_forward_cond = z3.And(
                forward_cond_copy, case_match)
            case_block.eval(ctx)
            if not (ctx.has_returned or ctx.get_exited()):
                then_vars = ctx.get_attrs()
                case_exprs.append((case_match, then_vars))
            ctx.has_returned = False
            ctx.set_exited(False)
            ctx.restore(var_store)
            case_matches.append(case_match)
        var_store = ctx.checkpoint()
        # process the default expression
        cond = z3.Not(z3.Or(*case_matches))
        if not z3.is_false(cond):
            ctx.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            self.default_case.eval(ctx)
            if ctx.has_returned or ctx.get_exited():
                ctx.restore(var_store)
            ctx.has_returned = False
            ctx.set_exited(False)
            ctx.tmp_forward_cond = forward_cond_copy
        # merge all the expressions in reverse order
        for cond, then_vars in reversed(case_exprs):
            merge_attrs(ctx, cond, then_vars)

    def eval_switch_table_matches(self, ctx, table):
        cases = OrderedDict()
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
                match_cond = table.get_const_matches(ctx, c_keys)
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
            add_default = None
            for case_name, case_block in self.case_blocks.items():
                match_var = table.tbl_action
                action = table.actions[case_name][0]
                match_cond = z3.And(table.locals["hit"], (action == match_var))
                cases[case_name] = (match_cond, case_block)
                # we need to check if the default is in the cases
                # this implies that the "default" case can never be executed
                if case_name == table.default_action[1]:
                    add_default = (case_name, (z3.BoolVal(True), case_block))
            if add_default and len(table.actions) == len(cases):
                cases[add_default[0]] = add_default[1]
        return cases

    def eval_switch_expr_matches(self, ctx, switch_expr):
        cases = {}
        for case_val, case_block in self.case_blocks.items():
            # assume the value has no side-effects
            case_val = ctx.resolve_expr(case_val)
            match_cond = switch_expr == case_val
            cases[case_val] = (match_cond, case_block)
        return cases

    def eval(self, ctx):
        switch_expr = ctx.resolve_expr(self.switch_expr)
        if isinstance(switch_expr, P4Table):
            # check whether we are dealing with a table switch case
            cases = self.eval_switch_table_matches(ctx, table=switch_expr)
        else:
            # or just a general switch case on an expression
            cases = self.eval_switch_expr_matches(ctx, switch_expr)
        self.eval_cases(ctx, cases)


class P4Noop(P4Statement):

    def eval(self, ctx):
        pass


class P4Return(P4Statement):
    def __init__(self, expr=None):
        self.expr = expr

    def eval(self, ctx):

        if self.expr is None:
            expr = None
        else:
            # resolve the expr before restoring the state
            expr = ctx.resolve_expr(self.expr)
            if isinstance(ctx.return_type, z3.BitVecSortRef):
                expr = z3_cast(expr, ctx.return_type)
            # we return a complex typed expression list, instantiate
            if isinstance(expr, list):
                # name is meaningless here so keep it empty
                instance = ctx.gen_instance("", ctx.return_type)
                instance.set_list(expr)
                expr = instance

        cond = z3.simplify(z3.And(z3.Not(z3.Or(*ctx.forward_conds)),
                                  ctx.tmp_forward_cond))
        if not z3.is_false(cond):
            ctx.return_states.append((cond, ctx.copy_attrs()))
            if expr is not None:
                ctx.return_exprs.append((cond, expr))
            ctx.has_returned = True
        ctx.forward_conds.append(ctx.tmp_forward_cond)


class P4Exit(P4Statement):

    def eval(self, ctx):
        # FIXME: This checkpointing should not be necessary
        # Figure out what is going on
        var_store = ctx.checkpoint()
        forward_conds = []
        tmp_forward_conds = []
        sub_ctx = ctx
        while not isinstance(sub_ctx, StaticContext):
            sub_ctx.copy_out(ctx)
            forward_conds.extend(sub_ctx.forward_conds)
            tmp_forward_conds.append(sub_ctx.tmp_forward_cond)
            sub_ctx = sub_ctx.parent_ctx

        cond = z3.simplify(z3.And(z3.Not(z3.Or(*forward_conds)),
                                  z3.And(*tmp_forward_conds)))
        if not z3.is_false(cond):
            ctx.add_exit_state(
                cond, ctx.get_p4_state().get_members(ctx))
            ctx.set_exited(True)
        ctx.restore(var_store)
        ctx.forward_conds.append(ctx.tmp_forward_cond)
