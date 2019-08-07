from z3 import *
import os
import operator


def step(func_chain, inouts, expr=None):
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    fun_expr = None
    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        # emulate pass-by-value behavior
        inouts = copy.deepcopy(inouts)
        fun_expr = next_fun(func_chain, inouts)
    # print("#################################")
    # print("EXPR")
    # print(expr)
    # print("FUN_EXPR")
    # print(fun_expr)
    if fun_expr is not None and expr is not None:
        # print("CONCATENATING")
        return And(expr, fun_expr)
    elif fun_expr is not None:
        # print("EXTRACTING")
        return fun_expr
    elif expr is not None:
        # print("JUST RETURNING")
        return expr
    else:
        # print("RETURNING TRUE")
        return True


def step_old(func_chain, inouts, expr=True):
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        # emulate pass-by-value behavior
        inouts = copy.deepcopy(inouts)
        expr = next_fun(func_chain, inouts)
    return expr


def slice_assign(lval, rval, range):
    lval_max = lval.size() - 1
    slice_l = range[0]
    slice_r = range[1]
    if slice_l == lval_max and slice_r == 0:
        return rval
    assemble = []
    if (slice_l < lval_max):
        assemble.append(Extract(lval_max, slice_l + 1, lval))
    assemble.append(rval)
    if (slice_r > 0):
        assemble.append(Extract(slice_r - 1, 0, lval))
    return Concat(*assemble)


class Z3Registry():
    reg = {}

    def __init__(self):
        pass

    def register_z3_type(self, name, p4_class, z3_args):
        z3_type = name
        z3_class = name.upper()
        self.reg[z3_type] = Datatype(z3_type)
        self.reg[z3_type].declare(f"mk_{z3_type}", *z3_args)
        self.reg[z3_type] = self.reg[z3_type].create()

        self.reg[z3_class] = type(name.upper(), (p4_class,), {})


z3_reg = Z3Registry()


class Header():

    def __init__(self):
        self.set_basic_attrs()
        self.constructor = self.z3_type.constructor(0)
        self.const = Const(f"{self.name}_0", self.z3_type)
        self.revisions = [self.const]
        self.accessors = self.generate_accessors(
            self.z3_type, self.constructor)

        # These are special for headers
        self.set_hdr_accessors()
        self.set_valid()

    def set_basic_attrs(self):
        cls_name = self.__class__.__name__.lower()
        cls_id = str(id(self))[-4:]
        self.name = "%s%s" % (cls_name, cls_id)
        self.z3_type = z3_reg.reg[cls_name]

    def generate_accessors(self, z3_type, constructor):
        accessors = []
        for type_index in range(constructor.arity()):
            accessors.append(z3_type.accessor(0, type_index))
        return accessors

    def set_hdr_accessors(self):
        for accessor in self.accessors:
            setattr(self, accessor.name(), accessor(self.const))

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", self.z3_type)
        self.revisions.append(self.const)

    def make(self):
        members = []
        for accessor in self.accessors:
            members.append(getattr(self, accessor.name()))
        return self.constructor(*members)

    def set(self, lstring, rvalue):
        # update the internal representation of the attribute
        lvalue = operator.attrgetter(lstring)(self)
        prefix, suffix = lstring.rsplit(".", 1)
        target_class = operator.attrgetter(prefix)(self)
        setattr(target_class, suffix, rvalue)
        # generate a new version of the z3 datatype
        copy = self.make()
        # update the SSA version
        self.update()
        # return the update expression
        return (self.const == copy)

    def set_valid(self):
        cls_name = self.__class__.__name__.lower()
        self.valid = Const("%s_valid" % cls_name, BoolSort())

    def isValid(self):
        return self.valid

    def setValid(self):
        self.valid = True

    def setInvalid(self):
        self.valid = False


class Struct():

    def __init__(self):
        self.set_basic_attrs()
        self.constructor = self.z3_type.constructor(0)
        self.const = Const(f"{self.name}_0", self.z3_type)
        self.revisions = [self.const]
        self.accessors = self.generate_accessors(
            self.z3_type, self.constructor)

        # These are special for structs
        self.set_struct_accessors()

    def set_basic_attrs(self):
        cls_name = self.__class__.__name__.lower()
        cls_id = str(id(self))[-4:]
        self.name = "%s%s" % (cls_name, cls_id)
        self.z3_type = z3_reg.reg[cls_name]

    def generate_accessors(self, z3_type, constructor):
        accessors = []
        for type_index in range(constructor.arity()):
            accessors.append(z3_type.accessor(0, type_index))
        return accessors

    def set_struct_accessors(self):
        for accessor in self.accessors:
            arg_type = accessor.range()
            is_datatype = type(arg_type) == (DatatypeSortRef)
            if is_datatype:
                member_cls = z3_reg.reg[arg_type.name().upper()]
                setattr(self, accessor.name(), member_cls())
            else:
                setattr(self, accessor.name(), accessor(self.const))

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", self.z3_type)
        self.revisions.append(self.const)

    def make(self):
        members = []
        for accessor in self.accessors:
            arg_type = accessor.range()
            is_datatype = type(arg_type) == (DatatypeSortRef)
            if is_datatype:
                member_make = operator.attrgetter(
                    accessor.name() + ".make")(self)
                members.append(member_make())
            else:
                member_make = operator.attrgetter(accessor.name())(self)
                members.append(member_make)
        return self.constructor(*members)

    def set(self, lstring, rvalue):
        # update the internal representation of the attribute
        lvalue = operator.attrgetter(lstring)(self)
        prefix, suffix = lstring.rsplit(".", 1)
        target_class = operator.attrgetter(prefix)(self)
        setattr(target_class, suffix, rvalue)
        # generate a new version of the z3 datatype
        copy = self.make()
        # update the SSA version
        self.update()
        # return the update expression
        return (self.const == copy)


class Table():

    @classmethod
    def table_action(cls, func_chain, inouts):
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
            expr = Implies(cls.ma.action(cls.m) == f_id,
                           f_fun(func_chain, inouts, *f_args))
            actions.append(expr)
        return And(*actions)

    @classmethod
    def table_match(cls, inouts):
        raise NotImplementedError

    @classmethod
    def action_run(cls, inouts):
        return If(cls.table_match(inouts),
                  cls.ma.action(cls.m),
                  0)

    @classmethod
    def apply(cls, func_chain, inouts):
        # This is a table match where we look up the provided key
        # If we match select the associated action,
        # else use the default action
        def_fun = cls.actions["default"][1][0]
        def_args = cls.actions["default"][1][1]
        return If(cls.table_match(inouts),
                  cls.table_action(func_chain, inouts),
                  def_fun(func_chain, inouts, *def_args))
