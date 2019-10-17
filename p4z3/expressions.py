from copy import deepcopy
from collections import OrderedDict
import logging as log
from p4z3.base import *


def step(p4_vars, expr_chain, expr=None) -> z3.ExprRef:
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if expr_chain:
        # pop the first function in the list
        next_expr = expr_chain.pop(0)
        # emulate pass-by-value behavior
        # this is necessary to for state branches
        # p4_vars = deepcopy(p4_vars)
        expr_chain = list(expr_chain)
        # iterate through all the remaining functions in the chain
        fun_expr = next_expr.eval(p4_vars, expr_chain)
        if not isinstance(fun_expr, z3.ExprRef):
            raise TypeError(f"Expression {fun_expr} is not a z3 expression!")
        # eval should always return an expression
        if expr is not None:
            # concatenate chain result with the provided expression
            # return z3.And(expr, fun_expr)
            # actually, there is no need to chain.
            # so let's return the normal expression for now
            return fun_expr
        else:
            # extract the chained result
            return fun_expr
    if expr is not None:
        # end of chain, just mirror the passed expressions
        return expr
    else:
        # empty statement, just return the final update assignment
        z3_copy = p4_vars._make(p4_vars.const)
        return p4_vars.const == z3_copy


def resolve_expr(p4_vars, expr_chain, val) -> z3.SortRef:
    # Resolves to z3 and z3p4 expressions, bools and int are also okay
    val_str = val
    # resolve potential string references first
    if isinstance(val, str):
        val = p4_vars.get_var(val)
    if val is None:
        raise RuntimeError(
            f"Variable {val_str} does not exist in current environment!")
    if isinstance(val, (z3.ExprRef, bool, int)):
        # These are z3 types and can be returned
        return val
    if isinstance(val, P4Z3Type):
        # We got a P4 type, recurse...
        return step(p4_vars, [val] + expr_chain)
    if isinstance(val, P4ComplexType):
        # If we get a whole class return the complex z3 type
        return val
    raise RuntimeError(f"Value of type {type(val)} cannot be resolved!")


class P4Z3Type():
    def eval(self, p4_vars, expr_chain):
        raise NotImplementedError("Method eval not implemented!")


class MethodCallExpr(P4Z3Type):

    def __init__(self, expr, *args):
        self.expr = expr
        self.args = args

    def set_args(self, args):
        self.args = args

    def eval(self, p4_vars, expr_chain):
        p4_method = self.expr
        if isinstance(self.expr, str):
            p4_method = p4_vars.get_var(self.expr)
        if callable(p4_method):
            return p4_method(p4_vars, expr_chain, *self.args)
        if isinstance(p4_method, P4Action):
            p4_method.set_param_args(arg_prefix="")
            p4_method.merge_args(p4_vars, expr_chain, self.args)
            return step(p4_vars, [p4_method] + expr_chain)
        raise RuntimeError(f"Unsupported method type {type(p4_method)}!")


class P4BinaryOp(P4Z3Type):
    def __init__(self, lval, rval, operator):
        self.lval = lval
        self.rval = rval
        self.operator = operator

    def eval(self, p4_vars, expr_chain):
        lval_expr = resolve_expr(p4_vars, expr_chain, self.lval)
        rval_expr = resolve_expr(p4_vars, expr_chain, self.rval)
        return self.operator(lval_expr, rval_expr)


class P4UnaryOp(P4Z3Type):
    def __init__(self, val, operator):
        self.val = val
        self.operator = operator

    def eval(self, p4_vars, expr_chain):
        expr = resolve_expr(p4_vars, expr_chain, self.val)
        return self.operator(expr)


class P4not(P4UnaryOp):
    def __init__(self, val):
        operator = z3.Not
        P4UnaryOp.__init__(self, val, operator)


class P4abs(P4UnaryOp):
    def __init__(self, val):
        operator = op.abs
        P4UnaryOp.__init__(self, val, operator)


class P4inv(P4UnaryOp):
    def __init__(self, val):
        operator = op.inv
        P4UnaryOp.__init__(self, val, operator)


class P4neg(P4UnaryOp):
    def __init__(self, val):
        operator = op.neg
        P4UnaryOp.__init__(self, val, operator)


class P4add(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.add
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4mul(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.mul
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4mod(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.mod
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4pow(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.pow
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4and(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.and_
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4or(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.or_
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4xor(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.xor
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4div(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.floordiv
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lshift(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.lshift
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4rshift(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.rshift
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lt(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.lt
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4le(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.le
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4eq(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.eq
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4ne(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.ne
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4ge(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.ge
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4gt(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.gt
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4Slice(P4Z3Type):
    def __init__(self, val, slice_l, slice_r):
        self.val = val
        self.slice_l = slice_l
        self.slice_r = slice_r

    def eval(self, p4_vars, expr_chain):
        val_expr = resolve_expr(p4_vars, expr_chain, self.val)
        return z3.Extract(self.slice_l, self.slice_r, val_expr)


class P4Concat(P4Z3Type):
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_vars, expr_chain):
        lval_expr = resolve_expr(p4_vars, expr_chain, self.lval)
        rval_expr = resolve_expr(p4_vars, expr_chain, self.rval)
        return z3.Concat(lval_expr, rval_expr)


class P4Cast(P4Z3Type):
    # TODO: need to take a closer look on how to do this correctly...
    # If we cast do we add/remove the least or most significant bits?
    def __init__(self, val, to_size):
        self.val = val
        self.to_size = to_size

    def eval(self, p4_vars, expr_chain):
        expr = resolve_expr(p4_vars, expr_chain, self.val)
        if expr.size() < self.to_size:
            return z3.ZeroExt(self.to_size - expr.size(), expr)
        else:
            slice_l = expr.size() - 1
            slice_r = expr.size() - self.to_size
            return z3.Extract(slice_l, slice_r, expr)


class P4Declaration(P4Z3Type):
    # TODO: Add some more declaration checks here.
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_vars, expr_chain):
        assign = AssignmentStatement(self.lval, self.rval)
        return step(p4_vars, [assign] + expr_chain)


class P4StructInitializer():
    def __init__(self, p4z3_type, **kwargs):
        if len(kwargs) != len(p4z3_type.accessors):
            raise RuntimeError(
                "Invalid number of arguments for struct initialization!")
        self.p4z3_type = p4z3_type
        self.members = kwargs

    def get_struct(self, p4_vars, expr_chain):
        for name, val in self.members.items():
            val_expr = resolve_expr(p4_vars, expr_chain, val)
            self.p4z3_type.set_member(name, val_expr)
        return self.p4z3_type


def slice_assign(lval, rval, slice_l, slice_r) -> z3.SortRef:
    lval_max = lval.size() - 1
    if slice_l == lval_max and slice_r == 0:
        return rval
    assemble = []
    if slice_l < lval_max:
        assemble.append(z3.Extract(lval_max, slice_l + 1, lval))
    assemble.append(rval)
    if slice_r > 0:
        assemble.append(z3.Extract(slice_r - 1, 0, lval))
    return z3.Concat(*assemble)


class SliceAssignment(P4Z3Type):
    def __init__(self, lval, rval, slice_l, slice_r):
        self.lval = lval
        self.rval = rval
        self.slice_l = slice_l
        self.slice_r = slice_r

    def eval(self, p4_vars, expr_chain):
        lval_expr = resolve_expr(p4_vars, expr_chain, self.lval)
        rval_expr = resolve_expr(p4_vars, expr_chain, self.rval)
        rval_expr = slice_assign(lval_expr, rval_expr,
                                 self.slice_l, self.slice_r)
        assign = AssignmentStatement(self.lval, rval_expr)
        return step(p4_vars, [assign] + expr_chain)


class AssignmentStatement(P4Z3Type):

    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_vars, expr_chain):
        if isinstance(self.rval, list):
            list_expr = []
            for val in self.rval:
                list_expr.append(resolve_expr(p4_vars, expr_chain, val))
            assign_expr = p4_vars.set_list(self.lval, list_expr)
        elif isinstance(self.rval, P4StructInitializer):
            rval_expr = self.rval.get_struct(p4_vars, expr_chain)
            assign_expr = p4_vars.set_or_add_var(self.lval, rval_expr)
        else:
            rval_expr = resolve_expr(p4_vars, expr_chain, self.rval)
            assign_expr = p4_vars.set_or_add_var(self.lval, rval_expr)
        return step(p4_vars, expr_chain, assign_expr)


class MethodCallStmt(P4Z3Type):

    def __init__(self, method_expr):
        self.method_expr = method_expr

    def eval(self, p4_vars, expr_chain):
        return step(p4_vars, [self.method_expr] + expr_chain)


class BlockStatement(P4Z3Type):

    def __init__(self):
        self.exprs = []

    def add(self, expr):
        self.exprs.append(expr)

    def eval(self, p4_vars, expr_chain):
        return step(p4_vars, self.exprs + expr_chain)


class P4Action(P4Z3Type):

    def __init__(self):
        self.block = None
        self.parameters = []
        self.args = []

    def add_parameter(self, arg_name, arg_type):
        self.parameters.append((arg_name, arg_type))

    def add_stmt(self, block):
        if not isinstance(block, BlockStatement):
            raise RuntimeError(f"Expected a block, got {block}!")
        self.block = block

    def get_parameters(self):
        return self.parameters

    def set_param_args(self, arg_prefix):

        action_args = []
        for param in self.parameters:
            arg_name = param[0]
            arg_type = param[1]
            if isinstance(arg_type, z3.SortRef):
                action_args.append(
                    z3.Const(f"{arg_prefix}{arg_name}", arg_type))
            else:
                action_args.append(arg_type)
        self.args = action_args

    def merge_args(self, p4_vars, expr_chain, *args):
        if len(*args) > len(self.args):
            raise RuntimeError(
                f"Provided arguments {args} exceeds possible number of parameters.")
        for index, runtime_arg in enumerate(*args):
            self.args[index] = resolve_expr(p4_vars, expr_chain, runtime_arg)

    def eval(self, p4_vars, expr_chain):
        # var_buffer = {}
        # for action_arg in self.parameters:
        #     arg_name = action_arg[0]
        #     # previous previous variables in the environment
        #     try:
        #         prev_val = p4_vars.get_var(arg_name)
        #         var_buffer[arg_name] = prev_val
        #     except AttributeError:
        #         # ignore variables that do not exist
        #         pass

        # override the symbolic entries if we have concrete
        # arguments from the table
        for index, arg in enumerate(self.args):
            arg_name = self.parameters[index][0]
            p4_vars.set_or_add_var(arg_name, arg)

        # execute the action expression with the new environment
        expr = step(p4_vars, [self.block] + expr_chain)

        # reset the variables that were overwritten to their previous value
        # apparently p4 actions are pass by reference? So ignore that...
        # for action_arg in self.parameters:
        #     p4_vars.del_var(action_arg[0])
        # for arg_name, arg_expr in var_buffer.items():
        #     p4_vars.set_or_add_var(arg_name, arg_expr)
        return expr


class IfStatement(P4Z3Type):

    def __init__(self):
        self.condition = None
        self.then_block = None
        self.else_block = None

    def add_condition(self, condition):
        self.condition = condition

    def add_then_stmt(self, stmt):
        self.then_block = stmt

    def add_else_stmt(self, stmt):
        self.else_block = stmt

    def eval(self, p4_vars, expr_chain):
        if self.condition is None:
            raise RuntimeError("Missing condition!")
        condition = resolve_expr(p4_vars, expr_chain, self.condition)
        if self.else_block:
            if_expr = step(deepcopy(p4_vars), [
                self.then_block] + expr_chain)
            then_expr = step(deepcopy(p4_vars), [
                self.then_block] + expr_chain)
            return z3.If(condition, if_expr, then_expr)
        else:
            return z3.Implies(condition,
                              step(deepcopy(p4_vars),
                                   [self.then_block] + expr_chain))


class SwitchStatement(P4Z3Type):

    def __init__(self, table):
        self.table = table
        self.default_case = BlockStatement()
        self.cases = OrderedDict()

    def add_case(self, action_str):
        table = self.table
        action = table.actions[action_str]
        action_var = z3.Int(f"{table.name}_action")
        case = {}
        case["match"] = (action_var == action[0])
        # case["action_fun"] = action[1]
        case["case_block"] = BlockStatement()
        self.cases[action_str] = case

    def add_stmt_to_case(self, action_str, case_stmt):
        case_block = self.cases[action_str]["case_block"]
        case_block.add(case_stmt)

    def add_stmt_to_default(self, default_stmt):
        self.default_case.add(default_stmt)

    def eval(self, p4_vars, expr_chain):
        class SwitchHit():
            def __init__(self, cases):
                self.cases = cases

            def eval(self, p4_vars, expr_chain):
                case_exprs = []
                for case_name, case in self.cases.items():
                    case_block = step(
                        deepcopy(p4_vars), [case["case_block"]] + expr_chain)
                    case_exprs.append(z3.Implies(case["match"], case_block))
                return z3.And(*case_exprs)
        switch_hit = SwitchHit(self.cases)
        switch_default = self.default_case
        switch_if = IfStatement()
        switch_if.add_condition(self.table.table_match(p4_vars, expr_chain))
        switch_if.add_then_stmt(switch_hit)
        switch_if.add_else_stmt(switch_default)
        return z3.And(step(p4_vars, [self.table] + expr_chain),
                      step(p4_vars, [switch_if] + expr_chain))


class P4Table(P4Z3Type):

    def __init__(self, name):
        self.name = name
        self.keys = []
        self.actions = OrderedDict()

    def table_action(self, p4_vars, expr_chain):
        action = z3.Int(f"{self.name}_action")
        ''' This is a special macro to define action selection. We treat
        selection as a chain of implications. If we match, then the clause
        returned by the action must be valid.
        '''
        actions = []
        for f_name, f_tuple in self.actions.items():
            p4_action_id = f_tuple[0]
            if p4_action_id == 0:
                continue
            action_expr = self.execute_action(p4_vars, expr_chain, f_tuple)
            expr = z3.Implies(action == p4_action_id, action_expr)
            actions.append(expr)
        return z3.And(*actions)

    def add_action(self, p4_vars, action_expr):
        # TODO Fix this roundabout way of getting a P4 Action,
        #  super annoying...
        expr_name = action_expr.expr
        if not isinstance(expr_name, str):
            raise RuntimeError(f"Expected a string, got {type(expr_name)}!")
        p4_action = p4_vars.get_var(expr_name)
        if not isinstance(p4_action, P4Action):
            raise RuntimeError(f"Expected a P4Action got {type(p4_action)}!")
        index = len(self.actions) + 1
        self.actions[expr_name] = (index, p4_action, action_expr.args)

    def add_default(self, p4_vars, action_expr):
        expr_name = action_expr.expr
        if not isinstance(expr_name, str):
            raise RuntimeError(f"Expected a string, got {type(expr_name)}!")
        p4_action = p4_vars.get_var(expr_name)
        if not isinstance(p4_action, P4Action):
            raise RuntimeError(f"Expected a P4Action got {type(p4_action)}!")
        self.actions["default"] = (0, p4_action, action_expr.args)

    def add_match(self, table_key):
        self.keys.append(table_key)

    def table_match(self, p4_vars, expr_chain):
        key_pairs = []
        if not self.keys:
            # there is nothing to match with...
            return False
        for index, key in enumerate(self.keys):
            key_eval = resolve_expr(p4_vars, expr_chain, key)
            key_match = z3.Const(f"{self.name}_key_{index}", key_eval.sort())
            key_pairs.append(key_eval == key_match)
        return z3.And(key_pairs)

    def execute_action(self, p4_vars, expr_chain, action_tuple):
        p4_action = action_tuple[1]
        p4_vars = deepcopy(p4_vars)
        p4_action.set_param_args(arg_prefix=self.name)
        p4_action.merge_args(p4_vars, expr_chain, action_tuple[2])
        action_expr = step(p4_vars, [p4_action] + expr_chain)
        return action_expr

    def apply(self, p4_vars, expr_chain):
        return step(p4_vars, [self] + expr_chain)

    def eval(self, p4_vars, expr_chain):
        # This is a table match where we look up the provided key
        # If we match select the associated action,
        # else use the default action
        def_expr = self.execute_action(
            p4_vars, expr_chain, self.actions["default"])
        return z3.If(self.table_match(p4_vars, expr_chain),
                     self.table_action(p4_vars, expr_chain),
                     def_expr)
