from collections import OrderedDict
import z3

from p4z3.base import log, copy_attrs, DefaultExpression, copy, z3_cast
from p4z3.base import P4ComplexInstance, P4Statement, P4Z3Class, Z3If
from p4z3.callables import P4Callable, P4Context


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

        # this check only exists for exit statements
        is_data_type = isinstance(rval_expr, z3.DatatypeRef)
        if is_data_type and (rval_expr.sort() == p4_state.sort()):
            return rval_expr
        p4_state.set_or_add_var(self.lval, rval_expr)

        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class MethodCallStmt(P4Statement):

    def __init__(self, method_expr):
        self.method_expr = method_expr

    def eval(self, p4_state):
        expr = self.method_expr.eval(p4_state)
        if isinstance(expr, P4Callable):
            args = self.method_expr.args
            kwargs = self.method_expr.kwargs
            expr = expr(p4_state, *args, **kwargs)
        if p4_state.expr_chain:
            p4z3_expr = p4_state.pop_next_expr()
            return p4z3_expr.eval(p4_state)
        else:
            return expr


class BlockStatement(P4Statement):

    def __init__(self, exprs):
        self.exprs = exprs

    def eval(self, p4_state):
        p4_state.insert_exprs(self.exprs)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class IfStatement(P4Statement):

    def __init__(self, cond, in_function, then_block, else_block=None):
        self.cond = cond
        self.then_block = then_block
        self.else_block = else_block
        self.in_function = in_function

    def eval(self, p4_state):
        cond = p4_state.resolve_expr(self.cond)
        var_store, chain_copy = p4_state.checkpoint()
        then_expr = self.then_block.eval(p4_state)
        then_vars = copy_attrs(p4_state.p4_attrs)
        p4_state.restore(var_store, chain_copy)
        if self.else_block:
            else_expr = self.else_block.eval(p4_state)
        else:
            p4z3_expr = p4_state.pop_next_expr()
            else_expr = p4z3_expr.eval(p4_state)
        # this is a temporary hack to deal with functions and their return
        if self.in_function:
            # need to propagate side effects, thankfully functions do not
            # support exit statements, otherwise this would not work
            p4_state.merge_attrs(cond, then_vars)
            # we hit a void function, just return the merged state...
            if not isinstance(then_expr, (z3.AstRef, int)):
                return p4_state.get_z3_obj()
            # some z3 shenaningens, nested expressions are arithrefs
            # but arithrefs are not accepted as proper type
            # z3 is really stupid sometimes...
            then_is_arith_ref = isinstance(then_expr, z3.ArithRef)
            else_is_arith_ref = isinstance(else_expr, z3.ArithRef)
            if then_is_arith_ref and not else_is_arith_ref:
                then_expr = z3_cast(then_expr, else_expr)
            if else_is_arith_ref and not then_is_arith_ref:
                else_expr = z3_cast(else_expr, then_expr)
            return z3.If(cond, then_expr, else_expr)
        else:
            return Z3If(cond, then_expr, else_expr)


class SwitchHit(P4Z3Class):
    def __init__(self, cases, default_case):
        self.default_case = default_case
        self.cases = cases
        self.table = None

    def eval_cases(self, p4_state, cases):
        case_exprs = []
        for case in reversed(cases.values()):
            var_store, chain_copy = p4_state.checkpoint()
            case_expr = case["case_block"].eval(p4_state)
            p4_state.restore(var_store, chain_copy)
            case_exprs.append((case["match"], case_expr))
        expr = self.default_case.eval(p4_state)
        for cond, case_expr in case_exprs:
            expr = Z3If(cond, case_expr, expr)
        return expr

    def set_table(self, table):
        self.table = table

    def eval_switch_matches(self, table):
        for case_name, case in self.cases.items():
            match_var = table.tbl_action
            action = table.actions[case_name][0]
            match_cond = z3.And(table.p4_attrs["hit"], (action == match_var))
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
        # instantiate the hit expression
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class P4Noop(P4Statement):

    def eval(self, p4_state):
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class P4Return(P4Statement):
    def __init__(self, expr=None):
        self.expr = expr

    def eval(self, p4_state):

        # resolve the expr before restoring the state
        if self.expr is None:
            expr = None
        else:
            expr = p4_state.resolve_expr(self.expr)

        chain_copy = p4_state.copy_expr_chain()
        # remove all expressions until we hit the end (typically a context)
        for p4z3_expr in chain_copy:
            p4_state.expr_chain.popleft()
            # this is tricky, we need to restore the state before returning
            # so update the p4_state and then move on to return the expression
            # this technique preserves the return value
            if isinstance(p4z3_expr, P4Context):
                p4z3_expr.restore_context(p4_state)
                break
        # since we popped the P4Context object that would take care of this
        # return the z3 expressions of the state AFTER restoring it
        if expr is None:
            # FIXME: issue1386 requires us to keep running down the chain...
            # Need to run down to the remaining execution path after the return.
            p4z3_expr = p4_state.pop_next_expr()
            expr = p4z3_expr.eval(p4_state)
        return expr


class P4Exit(P4Statement):

    def eval(self, p4_state):
        # Exit the chain early and absolutely
        chain_copy = p4_state.copy_expr_chain()
        # remove all expressions, if we hit a context on the way, update
        for p4z3_expr in chain_copy:
            p4_state.expr_chain.popleft()
            # this is tricky, we need to restore the state before returning
            # so update the p4_state and then move on to return the expression
            # this technique preserves the return value
            if isinstance(p4z3_expr, P4Context):
                p4z3_expr.restore_context(p4_state)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)
