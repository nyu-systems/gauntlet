from z3 import *
import os
import operator

constants = set([])


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

    def _make(self, parent_const=None):
        members = []
        for accessor in self.accessors:
            arg_type = accessor.range()
            is_datatype = type(arg_type) == (DatatypeSortRef)
            if is_datatype:
                member_make = operator.attrgetter(
                    accessor.name() + "._make")(self)
                sub_const = accessor(parent_const)
                members.append(member_make(sub_const))
            else:
                # member_make = accessor(parent_const)
                member_make = operator.attrgetter(accessor.name())(self)
                is_datatype = type(member_make) == (DatatypeSortRef)

                members.append(member_make)
        return self.constructor(*members)

    def propagate_type(self, parent_const=None):
        for accessor in self.accessors:
            member = operator.attrgetter(accessor.name())(self)
            if isinstance(member, Z3P4Class):
                member.propagate_type(accessor(parent_const))
            else:
                setattr(self, accessor.name(), accessor(parent_const))


class P4State(Z3P4Class):

    def __init__(self, z3_reg, z3_id=0):
        super(P4State, self).__init__(z3_reg, z3_id)
        # These are special for structs
        self._set_accessors(z3_reg)
        self.propagate_type(self.const)

    def _set_accessors(self, z3_reg):
        for accessor in self.accessors:
            arg_type = accessor.range()
            member_cls = z3_reg.instance(arg_type.name())
            setattr(self, accessor.name(), member_cls)

    def _update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_1", self.z3_type)
        self.revisions.append(self.const)
        constants.add(self.const)

    def get_var(self, var_string):
        # we are trying to access a base function
        # just remove the brackets and call the result
        if (var_string.endswith("()")):
            var_string = var_string[:-2]
            return operator.attrgetter(var_string)(self)()
        else:
            return operator.attrgetter(var_string)(self)

    def del_var(self, var_string):
        return operator.attrgetter(var_string)(self)

    def set_or_add_var(self, lstring, rvalue):
        # update the internal representation of the attribute
        if ("." in lstring):
            prefix, suffix = lstring.rsplit(".", 1)
            target_class = operator.attrgetter(prefix)(self)
            setattr(target_class, suffix, rvalue)
            # generate a new version of the z3 datatype
            copy = self._make(self.const)
            # update the SSA version
            self._update()
            # return the update expression
            return (self.const == copy)
        else:
            setattr(self, lstring, rvalue)

    def set_or_add_struct(self, lstring, args):
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
            arg_type = accessor.range()
            is_datatype = type(arg_type) == (DatatypeSortRef)
            if is_datatype:
                member_cls = z3_reg.instance(arg_type.name())
                setattr(self, accessor.name(), member_cls)
            else:
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
        action = Int(f"{name}_action")
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
        action = Int(f"{name}_action")
        return cls.table_match(p4_vars)

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

    @classmethod
    def switch_apply(cls, func_chain, p4_vars, cases, default_case):
        def_fun = cls.actions["default"][1][0]
        def_args = cls.actions["default"][1][1]
        is_hit = cls.action_run(p4_vars)
        switch_hit = And((*cases), def_fun(func_chain, p4_vars, *def_args))
        switch_default = default_case(func_chain, p4_vars)
        return And(cls.apply(func_chain, p4_vars), If(is_hit, switch_hit, switch_default))

    @classmethod
    def case(cls, func_chain, p4_vars, action_str, case_block):
        action = cls.actions[action_str]

        action_var = Int(f"{cls.__name__}_action")
        return Implies(action_var == action[0], And(action[1][0](func_chain, p4_vars, *action[1][1]), case_block(func_chain, p4_vars)))


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


def z3_concat(left, right):
    return Concat(left, right)
