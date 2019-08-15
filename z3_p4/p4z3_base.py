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
    fun_expr = None
    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        # emulate pass-by-value behavior
        p4_vars = copy.deepcopy(p4_vars)
        fun_expr = next_fun(func_chain, p4_vars)
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


def step_old(func_chain, p4_vars, expr=True):
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        # emulate pass-by-value behavior
        p4_vars = copy.deepcopy(p4_vars)
        expr = next_fun(func_chain, p4_vars)
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


def output_update(func_chain, p4_vars, lval, rval):
    expr = p4_vars.set(lval, rval)
    return step(func_chain, p4_vars, expr)
