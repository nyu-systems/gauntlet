import operator as op
import z3


class P4ComplexType():
    def __init__(self, z3_reg, z3_type, name):
        self.name = name
        self.z3_type = z3_type
        self.const = z3.Const(f"{name}_0", z3_type)
        self.constructor = z3_type.constructor(0)
        # These are special for state
        self._set_z3_accessors(z3_type, self.constructor)
        self._init_members(z3_reg, self.accessors)

    def _set_z3_accessors(self, z3_type, constructor):
        self.accessors = []
        for type_index in range(constructor.arity()):
            accessor = z3_type.accessor(0, type_index)
            self.accessors.append(accessor)

    def _init_members(self, z3_reg, accessors):
        for accessor in accessors:
            arg_type = accessor.range()
            if isinstance(arg_type, z3.DatatypeSortRef):
                # this is a complex datatype, create a P4ComplexType
                member_cls = z3_reg.instance("", arg_type)
                # and add it to the members, this is a little inefficient...
                setattr(self, accessor.name(), member_cls)
                # since the type is dependent on its parent
                # we propagate the parent constant down to all members
                member_cls.propagate_type(accessor(self.const))
            else:
                # use the default z3 constructor
                setattr(self, accessor.name(), accessor(self.const))

    def _make(self, parent_const):
        members = []
        for accessor in self.accessors:
            member_make = op.attrgetter(accessor.name())(self)
            if isinstance(member_make, P4ComplexType):
                # it is a complex type
                # retrieve the accessor and call the c
                sub_const = accessor(parent_const)
                # call the constructor of the complex type
                members.append(member_make._make(sub_const))
            else:
                members.append(member_make)
        return self.constructor(*members)

    def set_member(self, accessor_name, val):
        # retrieve the member we are accessing
        member = op.attrgetter(accessor_name)(self)
        if isinstance(member, P4ComplexType):
            # it is a complex type
            # propagate the parent constant to all children
            member.propagate_type(val)
        else:
            # a simple z3 type, just update the constructor
            setattr(self, accessor_name, val)

    def propagate_type(self, parent_const: z3.AstRef):
        members = []
        for accessor in self.accessors:
            # a z3 constructor dependent on the parent constant
            z3_accessor = accessor(parent_const)
            self.set_member(accessor.name(), z3_accessor)
            members.append(z3_accessor)
        # generate the new z3 complex type out of all the sub constructors
        self.const = self.constructor(*members)


class P4State(P4ComplexType):

    def get_var(self, var_string):
        return op.attrgetter(var_string)(self)

    def del_var(self, var_string):
        delattr(self, var_string)

    def _update(self):
        self.const = z3.Const(f"{self.name}_1", self.z3_type)

    def set_or_add_var(self, lstring, rvalue):
        # update the internal representation of the attribute
        if '.' in lstring:
            # this means we are accessing a complex member
            # get the parent class and update its value
            # we do not want to recurse here
            prefix, suffix = lstring.rsplit(".", 1)
            target_class = op.attrgetter(prefix)(self)
            setattr(target_class, suffix, rvalue)
        else:
            setattr(self, lstring, rvalue)
        # generate a new version of the z3 datatype
        const_copy = self._make(self.const)
        # update the SSA version
        self._update()
        # return the update expression
        return self.const == const_copy

    def set_list(self, lstring, rvals):
        if '.' in lstring:
            prefix, suffix = lstring.rsplit(".", 1)
            target_class = op.attrgetter(prefix)(self)
        else:
            target_class = op.attrgetter(lstring)(self)
        if not isinstance(target_class, P4ComplexType):
            raise RuntimeError(
                "Trying to assign values to a non-complex type!")
        for index, rval in enumerate(rvals):
            accessor = target_class.accessors[index]
            setattr(target_class, accessor.name(), rval)
        # generate a new version of the z3 datatype
        const_copy = self._make(self.const)
        self._update()
        # return the update expression
        return self.const == const_copy

    def add_externs(self, externs):
        for extern_name, extern_method in externs.items():
            self.set_or_add_var(extern_name, extern_method)


class Header(P4ComplexType):

    def __init__(self, z3_reg, z3_type, const):
        super(Header, self).__init__(z3_reg, z3_type, const)

        # These are special for headers
        self.valid = z3.Const("%s_valid" % self.name, z3.BoolSort())

    def isValid(self, *args):
        return self.valid

    def setValid(self, *args):
        self.valid = True

    def setInvalid(self, *args):
        self.valid = False


class Struct(P4ComplexType):

    pass


def handle_type_stack(z3_args):
    fixed_args = []
    for z3_arg in z3_args:
        z3_name = z3_arg[0]
        z3_type = z3_arg[1]
        if isinstance(z3_type, list):
            for index, val in enumerate(z3_type):
                z3_tuple = (z3_name + "_%d" % index, val)
                fixed_args.append(z3_tuple)
        else:
            fixed_args.append(z3_arg)
    return fixed_args


class Z3Reg():
    _types = {}
    _externs = {}
    _classes = {}
    _ref_count = {}

    def register_structlike(self, name, p4_class, z3_args):
        self._types[name] = z3.Datatype(name)
        fixed_args = handle_type_stack(z3_args)
        self._types[name].declare(f"mk_{name}", *fixed_args)
        self._types[name] = self._types[name].create()
        # Add the
        self._classes[name] = p4_class
        self._ref_count[name] = 0

    def register_typedef(self, name, target):
        self._types[name] = target
        self._classes[name] = target
        self._ref_count[name] = 0

    def register_extern(self, name, method):
        self._externs[name] = method

    def register_stack(self, name, method):
        #TODO: Implement
        pass

    def reset(self):
        self._types.clear()
        self._classes.clear()
        self._ref_count.clear()

    def type(self, type_name):
        return self._types[type_name]

    def extern(self, extern_name):
        return self._externs[extern_name]

    def instance(self, var_name, p4z3_type: z3.SortRef):
        if isinstance(p4z3_type, z3.DatatypeSortRef):
            type_name = str(p4z3_type)
            z3_id = self._ref_count[type_name]
            name = "%s%d" % (type_name, z3_id)
            z3_cls = self._classes[type_name]
            self._ref_count[type_name] += 1
            return z3_cls(self, p4z3_type, name)
        else:
            return z3.Const(f"{var_name}", p4z3_type)
