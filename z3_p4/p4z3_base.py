from z3 import *
import os
import operator


class Z3Reg():
    types = {}
    _classes = {}
    _ref_count = {}

    def register_z3_type(self, name, p4_class, z3_args):
        self.types[name] = Datatype(name)
        self.types[name].declare(f"mk_{name}", *z3_args)
        self.types[name] = self.types[name].create()

        self._classes[name] = type(name, (p4_class,), {})
        self._ref_count[name] = 0

    def reset(self):
        self.types.clear()
        self._classes.clear()
        self._ref_count.clear()

    def instance(self, type_name):
        args = [self, self._ref_count[type_name]]
        z3_cls = self._classes[type_name](*args)
        self._ref_count[type_name] += 1
        return z3_cls


class Z3P4Class():
    def __init__(self, z3_reg, z3_id=0):
        self._set_basic_attrs(z3_reg, z3_id)
        self.constructor = self.z3_type.constructor(0)
        self.const = Const(f"{self.name}_0", self.z3_type)
        self.revisions = [self.const]
        self.accessors = self._generate_accessors(
            self.z3_type, self.constructor)

    def _set_basic_attrs(self, z3_reg, z3_id):
        cls_name = self.__class__.__name__
        self.name = "%s%d" % (cls_name, z3_id)
        self.z3_type = z3_reg.types[cls_name]

    def _generate_accessors(self, z3_type, constructor):
        accessors = []
        for type_index in range(constructor.arity()):
            accessors.append(z3_type.accessor(0, type_index))
        return accessors

    def _update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", self.z3_type)
        self.revisions.append(self.const)

    def _make(self):
        members = []
        for accessor in self.accessors:
            arg_type = accessor.range()
            is_datatype = type(arg_type) == (DatatypeSortRef)
            if is_datatype:
                member_make = operator.attrgetter(
                    accessor.name() + "._make")(self)
                members.append(member_make())
            else:
                member_make = operator.attrgetter(accessor.name())(self)
                members.append(member_make)
        return self.constructor(*members)


class P4State(Z3P4Class):

    def __init__(self, z3_reg, z3_id=0):
        super(P4State, self).__init__(z3_reg, z3_id)
        # These are special for structs
        self._set_accessors(z3_reg)

    def _set_accessors(self, z3_reg):
        for accessor in self.accessors:
            arg_type = accessor.range()
            member_cls = z3_reg.instance(arg_type.name())
            setattr(self, accessor.name(), member_cls)

    def set(self, lstring, rvalue):
        # update the internal representation of the attribute
        if ("." in lstring):
            prefix, suffix = lstring.rsplit(".", 1)
            target_class = operator.attrgetter(prefix)(self)
            setattr(target_class, suffix, rvalue)
            # generate a new version of the z3 datatype
            copy = self._make()
            # update the SSA version
            self._update()
            # return the update expression
            return (self.const == copy)
        else:
            setattr(self, lstring, rvalue)

    def set_struct(self, lstring, args):
        # this operation assumes that
        # args matches accessors in length
        members = []
        target_class = operator.attrgetter(lstring)(self)
        for index, accessor in enumerate(target_class.accessors):
            setattr(target_class, accessor.name(), args[index])
        # generate a new version of the z3 datatype
        # copy = self._make()
        # # update the SSA version
        # self._update()
        # # return the update expression
        # return (self.const == copy)


class Header(Z3P4Class):

    def __init__(self, z3_reg, z3_id=0):
        super(Header, self).__init__(z3_reg, z3_id)

        # These are special for headers
        self._set_hdr_accessors()
        self._init_valid()

    def _set_hdr_accessors(self):
        for accessor in self.accessors:
            setattr(self, accessor.name(), accessor(self.const))

    def _init_valid(self):
        self.valid = Const("%s_valid" % self.name, BoolSort())

    def isValid(self):
        return self.valid

    def setValid(self):
        self.valid = True

    def setInvalid(self):
        self.valid = False


class Struct(Z3P4Class):

    def __init__(self, z3_reg, z3_id=0):
        super(Struct, self).__init__(z3_reg, z3_id)

        # These are special for structs
        self._set_struct_accessors(z3_reg)

    def _set_struct_accessors(self, z3_reg):
        for accessor in self.accessors:
            arg_type = accessor.range()
            is_datatype = type(arg_type) == (DatatypeSortRef)
            if is_datatype:
                member_cls = z3_reg.instance(arg_type.name())
                setattr(self, accessor.name(), member_cls)
            else:
                setattr(self, accessor.name(), accessor(self.const))


class Table():

    @classmethod
    def table_action(cls, func_chain, p4_vars):
        name = cls.__name__
        action = Const(f"{name}_action", IntSort())
        ''' This is a special macro to define action selection. We treat
        selection as a chain of implications. If we match, then the clause
        returned by the action must be valid.
        '''
        actions = []
        for f_name, f_tuple in cls.actions.items():
            if f_name == "default":
                continue
            f_id = f_tuple[0]
            f_fun = f_tuple[1][0]
            f_args = f_tuple[1][1]
            expr = Implies(action == f_id,
                           f_fun(func_chain, p4_vars, *f_args))
            actions.append(expr)
        return And(*actions)

    @classmethod
    def table_match(cls, p4_vars):
        raise NotImplementedError

    @classmethod
    def action_run(cls, p4_vars):
        name = cls.__name__
        action = Const(f"{name}_action", IntSort())
        return If(cls.table_match(p4_vars),
                  action,
                  0)

    @classmethod
    def apply(cls, func_chain, p4_vars):
        # This is a table match where we look up the provided key
        # If we match select the associated action,
        # else use the default action
        def_fun = cls.actions["default"][1][0]
        def_args = cls.actions["default"][1][1]
        return If(cls.table_match(p4_vars),
                  cls.table_action(func_chain, p4_vars),
                  def_fun(func_chain, p4_vars, *def_args))


def step(func_chain, p4_vars, expr=None):
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if func_chain:
        # pop the first function in the list
        next_fun = func_chain.pop(0)
        # emulate pass-by-value behavior
        # this is necessary to for state branches
        p4_vars = copy.deepcopy(p4_vars)
        func_chain = list(func_chain)
        # iterate through all the remaining functions in the chain
        fun_expr = next_fun(func_chain, p4_vars)
        if expr is not None:
            # concatenate chain result with the provided expression
            return And(expr, fun_expr)
        else:
            # extract the chained result
            return fun_expr
    if expr is not None:
        # end of chain, just mirror the passed expressions
        return expr
    else:
        # empty statement, just return true
        return True


def slice_assign(lval, rval, slice_l, slice_r):
    lval_max = lval.size() - 1
    if slice_l == lval_max and slice_r == 0:
        return rval
    assemble = []
    if (slice_l < lval_max):
        assemble.append(Extract(lval_max, slice_l + 1, lval))
    assemble.append(rval)
    if (slice_r > 0):
        assemble.append(Extract(slice_r - 1, 0, lval))
    return Concat(*assemble)


def z3_cast(val, to_size):
    if (val.size() < to_size):
        return ZeroExt(to_size - val.size(), val)
    else:
        slice_l = val.size() - 1
        slice_r = val.size() - to_size
        return Extract(slice_l, slice_r, val)


def z3_slice(val, slice_l, slice_r):
    return Extract(slice_l, slice_r, val)


def step_alt(p4_vars, expr_chain=[], expr=None):
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if expr_chain:
        # emulate pass-by-value behavior
        # this is necessary to for state branches
        p4_vars = copy.deepcopy(p4_vars)
        expr_chain = list(expr_chain)
        # pop the first expression in the list
        next_expr = expr_chain.pop(0)
        # iterate through all the remaining functions in the chain
        fun_expr = next_expr.eval(p4_vars, expr_chain)
        if expr is not None:
            # concatenate chain result with the provided expression
            return And(expr, fun_expr)
        else:
            # extract the chained result
            return fun_expr
    if expr is not None:
        # end of chain, just mirror the passed expressions
        return expr
    else:
        # empty statement, just return true
        return True


class AssignmentStatement():
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_vars, expr_chain=[]):
        expr = p4_vars.set(self.lval, self.rval)
        return step_alt(p4_vars, expr_chain, expr)


class BlockStatement():
    def __init__(self):
        self.exprs = []

    def add(self, expr):
        self.exprs.append(expr)

    def eval(self, p4_vars, expr_chain=[]):
        return step_alt(p4_vars, self.exprs + expr_chain)


class Function():
    def __init__(self):
        self.block_statement = None

    def add(self, block_statement):
        self.block_statement = block_statement

    def eval(self, p4_vars, expr_chain=[]):
        return self.block_statement.eval(p4_vars, expr_chain)


class IfStatement():

    def __init__(self, condition, then_block, else_block):
        self.condition = condition
        self.then_block = then_block
        self.else_block = else_block

    def eval(self, p4_vars, expr_chain=[]):
        if (isinstance(self.condition, AstRef)):
            condition = self.condition
        else:
            condition = self.condition.eval(p4_vars, expr_chain)
        return If(condition, self.then_block.eval(p4_vars, expr_chain),
                  self.else_block.eval(p4_vars, expr_chain))


class TableExpr():

    @classmethod
    def table_action(cls, p4_vars, expr_chain=[]):
        name = cls.__name__
        action = Const(f"{name}_action", IntSort())
        ''' This is a special macro to define action selection. We treat
        selection as a chain of implications. If we match, then the clause
        returned by the action must be valid.
        '''
        actions = []
        for f_name, f_tuple in cls.actions.items():
            if f_name == "default":
                continue
            f_id = f_tuple[0]
            f_fun = f_tuple[1][0]
            f_args = f_tuple[1][1]
            expr = Implies(action == f_id,
                           f_fun(p4_vars, expr_chain, *f_args))
            actions.append(expr)
        return And(*actions)

    @classmethod
    def table_match(cls, p4_vars):
        raise NotImplementedError

    @classmethod
    def action_run(cls, p4_vars):
        name = cls.__name__
        action = Const(f"{name}_action", IntSort())
        return If(cls.table_match(p4_vars),
                  action,
                  0)

    @classmethod
    def apply(cls):
        return cls

    @classmethod
    def eval(cls, p4_vars, expr_chain=[]):
        # This is a table match where we look up the provided key
        # If we match select the associated action,
        # else use the default action
        def_fun = cls.actions["default"][1][0]
        def_args = cls.actions["default"][1][1]
        return If(cls.table_match(p4_vars),
                  cls.table_action(p4_vars, expr_chain),
                  def_fun(p4_vars, expr_chain, *def_args))
        return cls.apply(p4_vars, expr_chain)
