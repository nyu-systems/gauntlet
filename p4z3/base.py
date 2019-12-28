import operator as op
import os
import logging
import z3

log = logging.getLogger(__name__)
FILE_DIR = os.path.dirname(os.path.abspath(__file__))


def step(p4_state, expr_chain, expr=None) -> z3.ExprRef:
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if expr_chain:
        # pop the first function in the list
        next_expr = expr_chain.pop(0)
        expr_chain = list(expr_chain)
        # iterate through all the remaining functions in the chain
        log.debug("Evaluating %s", next_expr.__class__)
        expr = next_expr.eval(p4_state, expr_chain)
        # eval should always return an expression
        if not isinstance(expr, (z3.ExprRef)):
            raise TypeError(f"Expression {expr} is not a z3 expression!")
    if expr is not None:
        # end of chain, just mirror the passed expressions
        return expr
    else:
        # empty statement, just return the final update assignment
        z3_copy = p4_state._make(p4_state.const)
        return z3_copy


def z3_cast(val, to_size):
    val_size = val.size()
    if val_size < to_size:
        return z3.ZeroExt(to_size - val_size, val)
    else:
        slice_l = val_size - 1
        slice_r = val_size - to_size
        return z3.Extract(slice_l, slice_r, val)


class P4ComplexType():
    """
    A P4ComplexType is a wrapper for any type that is not a simple Z3 type
    such as IntSort, BitVecSort or BoolSort.
    A P4ComplexType creates an instance of a Z3 DataTypeRef, all subtypes
    become members of this class and be accessed in dot-notation
    (e.g., headers.eth.srcmac).
    If one of the children is a DataTypeRef a new P4ComplexType will be
    instantiated and attached as member.
    Every member of this class should either be a P4ComplexType or a z3.SortRef
     if it is a basic type. A DataTypeRef should never be a member and always
    needs to be converted to a P4ComplexType.
    """

    def __init__(self, z3_reg, z3_type: z3.SortRef, name):
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
                # since the child type is dependent on its parent
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
                # retrieve the accessor and call the constructor
                sub_const = accessor(parent_const)
                # call the constructor of the complex type
                members.append(member_make._make(sub_const))
            else:
                members.append(member_make)
        return self.constructor(*members)

    def _set_member(self, accessor_name, val):
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
            self._set_member(accessor.name(), z3_accessor)
            members.append(z3_accessor)
        # generate the new z3 complex type out of all the sub constructors
        self.const = self.constructor(*members)

    def get_var(self, var_string):
        try:
            var = op.attrgetter(var_string)(self)
        except AttributeError:
            return None
        return var

    def del_var(self, var_string):
        delattr(self, var_string)

    def resolve_reference(self, var):
        if isinstance(var, str):
            var = self.get_var(var)
            var = self.resolve_reference(var)
        return var

    def set_list(self, lstring, rvals):
        if '.' in lstring:
            prefix, suffix = lstring.rsplit(".", 1)
            target_class = self.get_var(prefix)
        else:
            target_class = self.get_var(lstring)
        if not isinstance(target_class, P4ComplexType):
            raise RuntimeError(
                "Trying to assign values to a non-complex type!")
        for index, rval in enumerate(rvals):
            accessor = target_class.accessors[index]
            target_class.set_or_add_var(accessor.name(), rval)

    def set_or_add_var(self, lstring, rval):
        # Check if the assigned variable is already a reference
        var = self.get_var(lstring)
        if var is None:
            # nothing found, just set the variable to the reference
            pass
        elif isinstance(var, str):
            # the target variable exists and is a string
            # this means it is a reference (i.e., pointer) to another
            # variable, so we need to resolve it
            log.debug("Found reference from %s to %s ", lstring, var)
            # because it is a reference  we are setting the actual target
            lstring = var
            # do not allow nested references, resolve the rvalue
            rval = self.resolve_reference(rval)
        else:
            # the target variable exists and is not a string
            # do not override an existing variable with a reference!
            # resolve any possible rvalue reference
            log.debug("Recursing with %s and %s ", lstring, rval)
            rval = self.resolve_reference(rval)

        # We also must handle integer values and convert them to bitvectors
        # For that we have to match the type
        if isinstance(rval, int):
            lval = self.resolve_reference(lstring)
            rval = z3.BitVecVal(rval, lval.size())
        elif isinstance(rval, list):
            self.set_list(lstring, rval)
            return

        log.debug("Setting %s(%s) to %s(%s) ",
                  lstring, type(lstring), rval, type(rval))
        if '.' in lstring:
            # this means we are accessing a complex member
            # get the parent class and update its value
            prefix, suffix = lstring.rsplit(".", 1)
            # prefix may be a pointer to an actual complex type, resolve it
            target_class = self.resolve_reference(prefix)
            target_class.set_or_add_var(suffix, rval)
        else:
            setattr(self, lstring, rval)

        # generate a new version of the z3 datatype
        # update the internal representation of the attribute.
        # this also checks the validity of the new assignment
        # if there is a type error, z3 will complain
        self.const = self._make(self.const)

    def __eq__(self, other):

        # It can happen that we compare to a list
        # comparisons are almost the same just do not use accessors
        if isinstance(other, P4ComplexType):
            other_list = other.accessors
        elif isinstance(other, list):
            other_list = other
        else:
            return z3.BoolVal(False)

        if len(self.accessors) != len(other_list):
            return z3.BoolVal(False)
        eq_accessors = []
        for index, self_access in enumerate(self.accessors):
            self_member = op.attrgetter(self_access.name())(self)
            other_member = other_list[index]
            if isinstance(other, P4ComplexType):
                other_member = op.attrgetter(other_member.name())(other)
            # we compare the members of each complex type
            z3_eq = self_member == other_member
            eq_accessors.append(z3_eq)
        return z3.And(*eq_accessors)


class P4State(P4ComplexType):

    def _update(self):
        self.const = z3.Const(f"{self.name}_1", self.z3_type)

    def set_or_add_var(self, lstring, rval):
        P4ComplexType.set_or_add_var(self, lstring, rval)
        self._update()

    def add_externs(self, externs):
        for extern_name, extern_method in externs.items():
            self.set_or_add_var(extern_name, extern_method)


class Header(P4ComplexType):

    def __init__(self, z3_reg, z3_type, name):
        # These are special for headers
        self.valid = z3.Bool(f"{name}_valid")
        super(Header, self).__init__(z3_reg, z3_type, name)

    def isValid(self, *args):
        return self.valid

    def setValid(self, p4_state, expr_chain):
        self.valid = z3.BoolVal(True)
        return step(p4_state, expr_chain)

    def setInvalid(self, p4_state, expr_chain):
        self.valid = z3.BoolVal(False)
        return step(p4_state, expr_chain)

    def __eq__(self, other):
        if isinstance(other, Header):
            # correspond to the P4 semantics for comparing headers
            # when both headers are invalid return true
            check_invalid = z3.And(z3.Not(self.isValid()),
                                   z3.Not(other.isValid()))
            # when both headers are valid compare the values
            check_valid = z3.And(self.isValid(), other.isValid())
            comparison = z3.And(check_valid, self.const == other.const)
            return z3.Or(check_invalid, comparison)
        return super().__eq__(other)


class HeaderUnion(P4ComplexType):
    # TODO: Implement this class correctly...

    def __init__(self, z3_reg, z3_type, const):
        # These are special for headers
        self.valid = z3.BoolSort()
        super(HeaderUnion, self).__init__(z3_reg, z3_type, const)

    def isValid(self, *args):
        return self.valid

    def setValid(self, p4_state, expr_chain):
        self.valid = z3.BoolVal(True)
        return step(p4_state, expr_chain)

    def setInvalid(self, p4_state, expr_chain):
        self.valid = z3.BoolVal(False)
        return step(p4_state, expr_chain)


class Struct(P4ComplexType):

    pass


class Enum(P4ComplexType):
    def __init__(self, z3_reg, z3_type: z3.SortRef, name):
        self.name = name
        self.z3_type = z3_type
        self.const = z3.BitVec(f"{self.name}", 8)
        self.constructor = z3_type.constructor(0)
        # These are special for enums
        self._set_z3_accessors(z3_type, self.constructor)
        self._init_members(z3_reg, self.accessors)

    def _set_z3_accessors(self, z3_type, constructor):
        self.accessors = []
        for type_index in range(constructor.arity()):
            accessor = z3_type.accessor(0, type_index)
            self.accessors.append(accessor)

    def _init_members(self, z3_reg, accessors):
        # Instead of a z3 variable we assign a concrete number to each member
        for idx, accessor in enumerate(accessors):
            setattr(self, accessor.name(), z3.BitVecVal(idx, 8))

    def propagate_type(self, parent_const: z3.AstRef):
        # Enums are static so they do not have variable types.
        pass


class Z3Reg():
    def __init__(self):
        self._types = {}
        self._externs = {}
        self._classes = {}
        self._ref_count = {}

    def _register_structlike(self, name, p4_class, z3_args):
        self._types[name] = z3.Datatype(name)
        self._types[name].declare(f"mk_{name}", *z3_args)
        self._types[name] = self._types[name].create()
        self._classes[name] = p4_class
        self._ref_count[name] = 0

    def register_header(self, name, z3_args):
        self._register_structlike(name, Header, z3_args)

    def register_struct(self, name, z3_args):
        self._register_structlike(name, Struct, z3_args)

    def register_enum(self, name, enum_args):
        # Enums are a bit weird... we first create a type
        enum_types = []
        for enum_name in enum_args:
            enum_types.append((enum_name, z3.BitVecSort(8)))
        self._register_structlike(name, Enum, enum_types)
        # And then actually instantiate it so we can reference it later
        self._externs[name] = self.instance(name, self._types[name])

    def register_inouts(self, name, z3_args):
        self._register_structlike(name, P4State, z3_args)

    def init_p4_state(self, name, z3_args):
        stripped_args = []
        for arg in z3_args:
            stripped_args.append((arg[1], arg[2]))
        self._register_structlike(name, P4State, stripped_args)
        p4_state = self.instance("", self.type(name))
        p4_state.add_externs(self._externs)
        return p4_state

    def register_typedef(self, name, target):
        self._types[name] = target
        self._classes[name] = target
        self._ref_count[name] = 0

    def register_extern(self, name, method):
        self._types[name] = z3.DeclareSort(name)
        self._externs[name] = method

    def register_method(self, name, method):
        self._externs[name] = method

    def reset(self):
        self._types.clear()
        self._classes.clear()
        self._ref_count.clear()

    def type(self, type_name):
        return self._types[type_name]

    def stack(self, z3_type, num):
        type_name = str(z3_type)
        z3_name = f"{type_name}{num}"
        stack_args = []
        for val in range(num):
            stack_args.append((f"{val}", z3_type))
        self.register_struct(z3_name, stack_args)
        return self.type(z3_name)

    def extern(self, extern_name):
        return self._externs[extern_name]

    def instance(self, var_name, p4z3_type: z3.SortRef):
        if isinstance(p4z3_type, z3.DatatypeSortRef):
            type_name = str(p4z3_type)
            z3_id = self._ref_count[type_name]
            name = "%s%d" % (type_name, z3_id)
            z3_cls = self._classes[type_name]
            self._ref_count[type_name] += 1
            instance = z3_cls(self, p4z3_type, name)
            instance.propagate_type(instance.const)
            return instance
        else:
            return z3.Const(f"{var_name}", p4z3_type)
