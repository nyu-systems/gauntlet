from collections import OrderedDict
import z3

from p4z3.base import log, copy_attrs, DefaultExpression, copy, z3_cast
from p4z3.base import P4ComplexInstance, P4Statement, P4Z3Class
from p4z3.callables import P4Context
from p4z3.expressions import P4Mux


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
        if isinstance(rval_expr, P4ComplexInstance):
            rval_expr = copy.copy(rval_expr)
        # make sure the assignment is aligned appropriately
        # this can happen because we also evaluate before the
        # BindTypeVariables pass
        # we can only align if tmp_val is a bitvector
        # example test: instance_overwrite.p4
        lval = p4_state.resolve_expr(self.lval)
        if isinstance(rval_expr, int) and isinstance(lval, (z3.BitVecSortRef, z3.BitVecRef)):
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
            if p4_state.has_exited or p4_state.contexts[-1].has_returned:
                break


class IfStatement(P4Statement):

    def __init__(self, cond, in_function, then_block, else_block=None):
        self.cond = cond
        self.then_block = then_block
        self.else_block = else_block
        self.in_function = in_function

    def eval(self, p4_state):
        context = p4_state.contexts[-1]
        cond = p4_state.resolve_expr(self.cond)
        var_store, chain_copy = p4_state.checkpoint()
        return_expr_copy = context.return_expr
        has_returned_copy = context.has_returned
        self.then_block.eval(p4_state)
        context.then_has_returned = context.has_returned
        then_expr = context.return_expr
        if context.has_returned:
            p4_state.check_validity()
            then_vars = copy_attrs(p4_state.locals)
            context.return_states.append((cond, then_vars))
        else:
            then_vars = copy_attrs(p4_state.locals)

        context.return_expr = return_expr_copy
        context.has_returned = has_returned_copy
        p4_state.restore(var_store, chain_copy)
        if self.else_block:
            else_expr = self.else_block.eval(p4_state)
        context.else_has_returned = context.has_returned
        else_expr = context.return_expr
        if context.else_has_returned:
            p4_state.check_validity()
            context.return_states.append((
                z3.Not(cond), copy_attrs(p4_state.locals)))
            p4_state.restore(var_store, chain_copy)
        elif not context.then_has_returned:
            p4_state.merge_attrs(cond, then_vars)

        context.return_expr = return_expr_copy
        context.has_returned = context.then_has_returned and context.else_has_returned
        # this is a temporary hack to deal with functions and their return
        if self.in_function:
            # need to propagate side effects, thankfully functions do not
            # support exit statements, otherwise this would not work
            if context.has_returned:
                if not isinstance(then_expr, (z3.AstRef, int)):
                    # sometimes we have more complex types, so we create a mux
                    mux = P4Mux(cond, then_expr, else_expr)
                    context.return_expr = mux.eval(p4_state)
                    return
                elif isinstance(then_expr, z3.DatatypeRef):
                    # we hit a void function, just return...
                    context.return_expr = None
                    return
                context.return_expr = z3.If(cond, then_expr, else_expr)
            elif context.then_has_returned:
                if then_expr is not None:
                    context.return_expr = (cond, then_expr)
            elif context.else_has_returned:
                if else_expr is not None:
                    context.return_expr = (cond, else_expr)


class SwitchHit(P4Z3Class):
    def __init__(self, cases, default_case):
        self.default_case = default_case
        self.cases = cases
        self.table = None

    def eval_cases(self, p4_state, cases):
        case_exprs = []
        for case in reversed(cases.values()):
            context = p4_state.contexts[-1]
            var_store, chain_copy = p4_state.checkpoint()
            return_expr_copy = context.return_expr
            has_returned_copy = context.has_returned
            case["case_block"].eval(p4_state)
            then_vars = copy_attrs(p4_state.locals)
            if context.has_returned:
                context.return_states.append((case["match"], then_vars))
            else:
                case_exprs.append((case["match"], then_vars))
            context.return_expr = return_expr_copy
            context.has_returned = has_returned_copy
            p4_state.restore(var_store, chain_copy)
        expr = self.default_case.eval(p4_state)
        for cond, then_vars in case_exprs:
            p4_state.merge_attrs(cond, then_vars)
        return expr

    def set_table(self, table):
        self.table = table

    def eval_switch_matches(self, table):
        for case_name, case in self.cases.items():
            match_var = table.tbl_action
            action = table.actions[case_name][0]
            match_cond = z3.And(table.locals["hit"], (action == match_var))
            self.cases[case_name]["match"] = match_cond

    def eval(self, p4_state):
        self.eval_switch_matches(self.table)
        switch_hit = self.eval_cases(p4_state, self.cases)
        return switch_hit


class SwitchStatement(P4Statement):
    def __init__(self, table_str, cases):
        self.table_str = table_str
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
        case["case_block"] = BlockStatement([])
        self.cases[action_str] = case

    def add_stmt_to_case(self, action_str, case_stmt):
        if isinstance(action_str, DefaultExpression):
            self.default_case = case_stmt
        else:
            self.cases[action_str]["case_block"] = case_stmt

    def eval(self, p4_state):
        switch_hit = SwitchHit(self.cases, self.default_case)
        p4_state.insert_exprs(switch_hit)
        table = self.table_str.eval(p4_state)
        switch_hit.set_table(table)
        switch_hit.eval(p4_state)


class P4Noop(P4Statement):

    def eval(self, p4_state):
        pass


class P4Return(P4Statement):
    def __init__(self, expr=None, z3_type=None):
        self.expr = expr
        self.z3_type = z3_type

    def eval(self, p4_state):
        context = p4_state.contexts[-1]
        context.has_returned = True
        # resolve the expr before restoring the state
        if self.expr is None:
            expr = None
        else:
            expr = p4_state.resolve_expr(self.expr)

        if isinstance(self.z3_type, z3.BitVecSortRef):
            expr = z3_cast(expr, self.z3_type)
        # we return a complex typed expression list, instantiate
        if isinstance(expr, list):
            instance = self.z3_type.instantiate("undefined")
            instance.set_list(expr)
            expr = instance
        if context.then_has_returned and context.return_expr is not None:
            cond, then_expr = context.return_expr
            if not isinstance(then_expr, (z3.AstRef, int)):
                # sometimes we have more complex types, so we create a mux
                mux = P4Mux(cond, then_expr, expr)
                context.return_expr = mux.eval(p4_state)
                return
            context.return_expr = z3.If(cond, then_expr, expr)
            context.then_has_returned = False
        elif context.else_has_returned and context.return_expr is not None:
            cond, else_expr = context.return_expr
            if not isinstance(else_expr, (z3.AstRef, int)):
                # sometimes we have more complex types, so we create a mux
                mux = P4Mux(cond, expr, else_expr)
                context.return_expr = mux.eval(p4_state)
                return
            context.return_expr = z3.If(cond, expr, else_expr)
            context.else_has_returned = False
        else:
            context.return_expr = expr


class P4Exit(P4Statement):

    def eval(self, p4_state):
        p4_state.has_exited = True
