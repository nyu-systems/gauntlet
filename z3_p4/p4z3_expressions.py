from p4z3_base import *
from collections import OrderedDict


def step(p4_vars, expr_chain=[], expr=None):
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if expr_chain:
        # pop the first function in the list
        next_expr = expr_chain.pop(0)
        # emulate pass-by-value behavior
        # this is necessary to for state branches
        p4_vars = copy.deepcopy(p4_vars)
        expr_chain = list(expr_chain)
        # iterate through all the remaining functions in the chain
        fun_expr = next_expr.eval(p4_vars, expr_chain)
        if expr is not None:
            # concatenate chain result with the provided expression
            # return And(expr, fun_expr)
            return fun_expr
        else:
            # extract the chained result
            return fun_expr
    if expr is not None:
        # end of chain, just mirror the passed expressions
        return expr
    else:
        # empty statement, just return true
        z3_copy = p4_vars._make(p4_vars.const)
        return (p4_vars.const == z3_copy)


class AssignmentStatement():
    def __init__(self):
        self.lval = None
        self.rval = None

    def add_assign(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_vars, expr_chain=[]):
        expr = p4_vars.set(self.lval, self.rval)
        return step(p4_vars, expr_chain, expr)


class BlockStatement():

    def __init__(self):
        self.exprs = []

    def add(self, expr):
        self.exprs.append(expr)

    def eval(self, p4_vars, expr_chain=[]):
        return step(p4_vars, self.exprs + expr_chain)


class ActionExpr():

    def __init__(self):
        self.block = BlockStatement()

    def add_stmt(self, stmt):
        self.block.add(stmt)

    def eval(self, p4_vars, expr_chain=[]):
        return self.block.eval(p4_vars, expr_chain)


class IfStatement():

    def __init__(self):
        self.condition = None
        self.then_block = BlockStatement()
        self.else_block = BlockStatement()

    def add_condition(self, condition):
        self.condition = condition

    def add_then_stmt(self, stmt):
        self.then_block.add(stmt)

    def add_else_stmt(self, stmt):
        self.else_block.add(stmt)

    def eval(self, p4_vars, expr_chain=[]):
        if (isinstance(self.condition, AstRef)):
            condition = self.condition
        else:
            condition = self.condition.eval(p4_vars, expr_chain)
        if self.else_block:
            return If(condition,
                      self.then_block.eval(p4_vars, expr_chain),
                      self.else_block.eval(p4_vars, expr_chain))
        else:
            return Implies(condition,
                           self.then_block.eval(p4_vars, expr_chain))


class SwitchStatement():

    def __init__(self, table):
        self.table = table
        self.default_case = BlockStatement()
        self.cases = OrderedDict()

    def add_case(self, action_str):
        table = self.table
        action = table.actions[action_str]
        action_var = Int(f"{table.name}_action")
        case = {}
        case["match"] = (action_var == action[0])
        case["action_fun"] = action[1]
        case["action_args"] = action[2]
        case["case_block"] = BlockStatement()
        self.cases[action_str] = case

    def add_stmt_to_case(self, action_str, case_stmt):
        case_block = self.cases[action_str]["case_block"]
        case_block.add(case_stmt)

    def add_stmt_to_default(self, default_stmt):
        self.default_case.add(default_stmt)

    def eval(self, p4_vars, expr_chain=[]):
        class SwitchHit():
            def __init__(self, cases):
                self.cases = cases

            def eval(self, p4_vars, expr_chain=[]):
                case_exprs = []
                for case_name, case in self.cases.items():
                    case_block = step(
                        p4_vars, [case["case_block"]] + expr_chain)
                    case_exprs.append(Implies(case["match"], case_block))
                return And(*case_exprs)
        switch_hit = SwitchHit(self.cases)
        switch_default = self.default_case
        switch_if = IfStatement()
        switch_if.add_condition(self.table.action_run(p4_vars))
        switch_if.add_then_stmt(switch_hit)
        switch_if.add_else_stmt(switch_default)
        return And(self.table.eval(p4_vars, expr_chain),
                   switch_if.eval(p4_vars, expr_chain))


class TableExpr():

    def __init__(self, name):
        self.name = name
        self.keys = []
        self.actions = {}

    def table_action(self, p4_vars, expr_chain=[]):
        action = Int(f"{self.name}_action")
        ''' This is a special macro to define action selection. We treat
        selection as a chain of implications. If we match, then the clause
        returned by the action must be valid.
        '''
        actions = []
        for f_name, f_tuple in self.actions.items():
            if f_name == "default":
                continue
            f_id = f_tuple[0]
            f_fun = f_tuple[1]
            f_args = f_tuple[2]
            expr = Implies(action == f_id,
                           f_fun(p4_vars, expr_chain, *f_args))
            actions.append(expr)
        return And(*actions)

    def add_action(self, str_name, action, *action_args):
        index = len(self.actions) + 1
        self.actions[str_name] = (index, action, action_args)

    def add_default(self, action, *action_args):
        self.actions["default"] = (0, action, action_args)

    def add_match(self, table_key):
        self.keys.append(table_key)

    def table_match(self, p4_vars):
        key_pairs = []
        for index, key in enumerate(self.keys):
            key_eval = key(p4_vars)
            key_match = Const(f"{self.name}_key_{index}", key_eval.sort())
            key_pairs.append(key_eval == key_match)
        return And(key_pairs)

    def action_run(self, p4_vars):
        action = Int(f"{self.name}_action")
        return self.table_match(p4_vars)

    def apply(self):
        return self

    def eval(self, p4_vars, expr_chain=[]):
        # This is a table match where we look up the provided key
        # If we match select the associated action,
        # else use the default action
        def_fun = self.actions["default"][1]
        def_args = self.actions["default"][2]
        return If(self.table_match(p4_vars),
                  self.table_action(p4_vars, expr_chain),
                  def_fun(p4_vars, expr_chain, *def_args))
