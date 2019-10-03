import operator as op
import z3


class Z3Reg():
    types = {}
    externs = {}
    _classes = {}
    _ref_count = {}

    def register_z3_type(self, name, p4_class, z3_args):
        self.types[name] = z3.Datatype(name)
        self.types[name].declare(f"mk_{name}", *z3_args)
        self.types[name] = self.types[name].create()

        self._classes[name] = type(name, (p4_class,), {})
        self._ref_count[name] = 0

    def register_extern(self, name, method):
        self.externs[name] = method

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
        self.const = z3.Const(f"{self.name}_0", self.z3_type)
        self.revisions = [self.const]
        self.accessors = self._generate_accessors(
            self.z3_type, self.constructor)

    def _set_basic_attrs(self, z3_reg, z3_id):
        cls_name = self.__class__.__name__
        self.name = "%s%d" % (cls_name, z3_id)
        self.z3_type = z3_reg.types[cls_name]

    def _set_accessors(self, z3_reg):
        for accessor in self.accessors:
            arg_type = accessor.range()
            if isinstance(arg_type, z3.DatatypeSortRef):
                member_cls = z3_reg.instance(arg_type.name())
                setattr(self, accessor.name(), member_cls)
            else:
                setattr(self, accessor.name(), accessor(self.const))

    def _generate_accessors(self, z3_type, constructor):
        accessors = []
        for type_index in range(constructor.arity()):
            accessors.append(z3_type.accessor(0, type_index))
        return accessors

    def _make(self, parent_const=None):
        members = []
        for accessor in self.accessors:
            arg_type = accessor.range()
            member_make = op.attrgetter(accessor.name())(self)
            if isinstance(member_make, Z3P4Class):
                sub_const = accessor(parent_const)
                members.append(member_make._make(sub_const))
            else:
                # member_make = accessor(parent_const)
                members.append(member_make)
        return self.constructor(*members)

    def propagate_type(self, parent_const=None):
        members = []
        for accessor in self.accessors:
            member = op.attrgetter(accessor.name())(self)
            if isinstance(member, Z3P4Class):
                member.propagate_type(accessor(parent_const))
                members.append(accessor(parent_const))
            else:
                setattr(self, accessor.name(), accessor(parent_const))
                members.append(accessor(parent_const))
        self.const = self.constructor(*members)

    def get_var(self, var_string):
        # we are trying to access a base function
        # just remove the brackets and try to call the result
        if var_string.endswith("()"):
            var_string = var_string[:-2]
            return op.attrgetter(var_string)(self)()
            # return op.methodcaller(var_string)(self)
        else:
            return op.attrgetter(var_string)(self)

    def del_var(self, var_string):
        delattr(self, var_string)

    def _update(self):
        # index = len(self.revisions)
        # self.const = z3.Const(f"{self.name}_{index}", self.z3_type)
        self.const = z3.Const(f"{self.name}_1", self.z3_type)
        self.revisions.append(self.const)

    def set_or_add_var(self, lstring, rvalue):
        # update the internal representation of the attribute
        if '.' in lstring:
            prefix, suffix = lstring.rsplit(".", 1)
            target_class = op.attrgetter(prefix)(self)
            setattr(target_class, suffix, rvalue)
            # generate a new version of the z3 datatype
            const_copy = self._make(self.const)
            # update the SSA version
            self._update()
            # return the update expression
            return self.const == const_copy
        else:
            setattr(self, lstring, rvalue)


class P4State(Z3P4Class):

    def __init__(self, z3_reg, z3_id=0):
        super(P4State, self).__init__(z3_reg, z3_id)
        self._set_accessors(z3_reg)

        # These are special for state
        self.propagate_type(self.const)

    def add_externs(self, externs):
        for extern_name, extern_method in externs.items():
            self.set_or_add_var(extern_name, extern_method)


class Header(Z3P4Class):

    def __init__(self, z3_reg, z3_id=0):
        super(Header, self).__init__(z3_reg, z3_id)
        self._set_accessors(z3_reg)

        # These are special for headers
        self.valid = z3.Const("%s_valid" % self.name, z3.BoolSort())

    def isValid(self, p4_vars, expr_chain):
        return self.valid

    def setValid(self):
        self.valid = True

    def setInvalid(self):
        self.valid = False


class Struct(Z3P4Class):

    def __init__(self, z3_reg, z3_id=0):
        super(Struct, self).__init__(z3_reg, z3_id)
        self._set_accessors(z3_reg)
