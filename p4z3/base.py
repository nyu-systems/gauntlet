import operator as op
from collections import deque
from copy import copy, deepcopy
import logging
import z3
from collections import OrderedDict

log = logging.getLogger(__name__)


def step(p4_state, expr=None):
    ''' The step function ensures that modifications are propagated to
        all subsequent operations. This is important to guarantee
        correctness with branching or local modification. '''
    if p4_state.expr_chain:
        # pop the first function in the list
        next_expr = p4_state.expr_chain.popleft()
        # iterate through all the remaining functions in the chain
        log.debug("Evaluating %s", next_expr.__class__)
        expr = next_expr.eval(p4_state)
        # eval should always return an expression
        if not isinstance(expr, (z3.ExprRef, int)):
            raise TypeError(f"Expression {expr} is not a z3 expression!")
    if expr is None:
        # empty statement, just return the final update assignment
        # this also checks the validity of the new assignment
        # if there is a type error, z3 will complain
        z3_copy = p4_state.get_z3_repr()
        return z3_copy
    # end of chain, just mirror the passed expressions
    return expr


def z3_cast(val, to_type):

    if isinstance(val, (z3.BoolSortRef, z3.BoolRef)):
        # Convert boolean variables to a bit vector representation
        # TODO: Streamline bools and their evaluation
        val = z3.If(val, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

    if isinstance(to_type, z3.BoolSortRef):
        # casting to a bool is simple, just check if the value is equal to 1
        # this works for bitvectors and integers, we convert any bools before
        return val == z3.BitVecVal(1, 1)

    # from here on we assume we are working with integer or bitvector types
    if isinstance(to_type, (z3.BitVecSortRef)):
        # It can happen that we get a bitvector type as target, get its size.
        to_type_size = to_type.size()
    else:
        to_type_size = to_type

    if isinstance(val, int):
        # It can happen that we get an int, cast it to a bit vector.
        return z3.BitVecVal(val, to_type_size)
    val_size = val.size()

    if val_size < to_type_size:
        # the target value is larger, extend with zeros
        return z3.ZeroExt(to_type_size - val_size, val)
    else:
        # the target value is smaller, truncate everything on the right
        return z3.Extract(to_type_size - 1, 0, val)


class P4Instance():
    def __new__(cls, z3_reg, method_name, *args, **kwargs):
        # parsed_args = []
        # for arg in args:
        #     arg = z3_reg._globals[arg]
        #     parsed_args.append(arg)
        # parsed_kwargs = {}
        # for name, arg in kwargs:
        #     arg = z3_reg._globals[arg]
        #     parsed_kwargs[name] = arg
        return z3_reg._globals[method_name](None, *args, **kwargs)


class P4Z3Class():
    def eval(self, p4_state):
        raise NotImplementedError("Method eval not implemented!")


class P4Expression(P4Z3Class):
    pass


class P4Statement(P4Z3Class):
    pass


class P4Package():

    def __init__(self, z3_reg, name, *args, **kwargs):
        self.pipes = OrderedDict()
        self.name = name
        self.z3_reg = z3_reg
        for arg in args:
            is_ref = arg[0]
            param_name = arg[1]
            param_sort = arg[2]
            self.pipes[param_name] = None

    def __call__(self, p4_state, *args, **kwargs):
        pipe_list = list(self.pipes.keys())
        merged_args = {}
        for idx, arg in enumerate(args):
            name = pipe_list[idx]
            merged_args[name] = arg
        for name, arg in kwargs.items():
            merged_args[name] = arg
        for name, arg in merged_args.items():
            # only add valid values
            if arg in self.z3_reg._globals:
                self.pipes[name] = self.z3_reg._globals[arg]
        return self


class P4Slice(P4Expression):
    def __init__(self, val, slice_l, slice_r):
        self.val = val
        self.slice_l = slice_l
        self.slice_r = slice_r

    def eval(self, p4_state):
        if isinstance(self.val, P4Expression):
            val_expr = self.val.eval(p4_state)
        else:
            val_expr = p4_state.resolve_reference(self.val)
        if isinstance(val_expr, int):
            val_expr = z3.BitVecVal(val_expr, 64)
        return z3.Extract(self.slice_l, self.slice_r, val_expr)


class P4ComplexType():
    """ A P4ComplexType is a wrapper for any type that is not a simple Z3 type
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
        self._init_members(z3_reg, self.const, self.accessors)

    def _set_z3_accessors(self, z3_type, constructor):
        self.accessors = []
        for type_index in range(constructor.arity()):
            accessor = z3_type.accessor(0, type_index)
            self.accessors.append(accessor)

    def _init_members(self, z3_reg, const, accessors):
        for accessor in accessors:
            arg_type = accessor.range()
            if isinstance(arg_type, z3.DatatypeSortRef):
                # this is a complex datatype, create a P4ComplexType
                member_cls = z3_reg.instance("", arg_type)
                # and add it to the members, this is a little inefficient...
                setattr(self, accessor.name(), member_cls)
                # since the child type is dependent on its parent
                # we propagate the parent constant down to all members
                member_cls.propagate_type(accessor(const))
            else:
                # use the default z3 constructor
                setattr(self, accessor.name(), accessor(const))

    def get_z3_repr(self, parent_const=None):
        members = []
        if parent_const is None:
            parent_const = self.const

        for accessor in self.accessors:
            member_make = op.attrgetter(accessor.name())(self)
            if isinstance(member_make, P4ComplexType):
                # it is a complex type
                # retrieve the accessor and call the constructor
                sub_const = accessor(parent_const)
                # call the constructor of the complex type
                members.append(member_make.get_z3_repr(sub_const))
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
        # this class is now dependent on its parent type
        # generate the new z3 complex type out of all the sub constructors
        self.const = self.constructor(*members)

    def get_var(self, var_string):
        try:
            var = op.attrgetter(var_string)(self)
        except AttributeError:
            return None
        return var

    def del_var(self, var_string):
        try:
            delattr(self, var_string)
        except AttributeError:
            log.warning(
                "Variable %s does not exist, nothing to delete!", var_string)

    def resolve_reference(self, var):
        log.debug("Resolving reference %s", var)
        if isinstance(var, str):
            var = self.get_var(var)
            var = self.resolve_reference(var)
        return var

    def find_nested_slice(self, lval, slice_l, slice_r):
        # gradually reduce the scope until we have calculated the right slice
        # also retrieve the string lvalue in the mean time
        if isinstance(lval, P4Slice):
            lval, outer_slice_l, outer_slice_r = self.find_nested_slice(
                lval.val, lval.slice_l, lval.slice_r)
            slice_l = outer_slice_r + slice_l
            slice_r = outer_slice_r + slice_r
        return lval, slice_l, slice_r

    def set_slice(self, lval, rval):
        slice_l = lval.slice_l
        slice_r = lval.slice_r
        lval = lval.val
        lval, slice_l, slice_r = self.find_nested_slice(lval, slice_l, slice_r)

        lval_expr = self.resolve_reference(lval)
        rval_expr = self.resolve_reference(rval)
        # stupid integer checks that are unfortunately necessary....
        if isinstance(lval_expr, int):
            lval_expr = z3.BitVecVal(lval_expr, 64)
        if isinstance(rval_expr, int):
            rval_expr = z3.BitVecVal(rval_expr, 64)
        lval_expr_max = lval_expr.size() - 1
        if slice_l == lval_expr_max and slice_r == 0:
            # slice is full lval, nothing to do
            self.set_or_add_var(lval, rval_expr)
            return
        assemble = []
        if slice_l < lval_expr_max:
            # left slice is smaller than the max, leave that chunk unchanged
            assemble.append(z3.Extract(lval_expr_max, slice_l + 1, lval_expr))
        # fill the rval_expr into the slice
        # this cast is necessary to match the margins and to handle integers
        rval_expr = z3_cast(rval_expr, slice_l + 1 - slice_r)
        assemble.append(rval_expr)
        if slice_r > 0:
            # right slice is larger than zero, leave that chunk unchanged
            assemble.append(z3.Extract(slice_r - 1, 0, lval_expr))
        rval_expr = z3.Concat(*assemble)
        self.set_or_add_var(lval, rval_expr)
        return

    def set_or_add_var(self, lval, rval):
        if isinstance(lval, P4Slice):
            return self.set_slice(lval, rval)
        # TODO: Fix this method, has hideous performance impact
        if hasattr(self, lval):
            tmp_lval = self.resolve_reference(lval)
            if isinstance(rval, list):
                tmp_lval.set_list(rval)
                return
            # We also must handle integer values and convert them to bitvectors
            # For that we have to match the type
            if isinstance(rval, int) and isinstance(tmp_lval, z3.BitVecRef):
                # if the lvalue is a bit vector, try to cast it
                # otherwise ignore and hope that keeping it as an int works out
                rval = z3.BitVecVal(rval, tmp_lval.size())
            # the target variable exists
            # do not override an existing variable with a string reference!
            # resolve any possible rvalue reference
            log.debug("Recursing with %s and %s ", lval, rval)
            rval = self.resolve_reference(rval)
        log.debug("Setting %s(%s) to %s(%s) ",
                  lval, type(lval), rval, type(rval))

        # now that all the preprocessing is done we can assign the value
        if '.' in lval:
            # this means we are accessing a complex member
            # get the parent class and update its value
            prefix, suffix = lval.rsplit(".", 1)
            # prefix may be a pointer to an actual complex type, resolve it
            target_class = self.resolve_reference(prefix)
            target_class.set_or_add_var(suffix, rval)
        else:
            setattr(self, lval, rval)

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

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        for name, val in result.__dict__.items():
            if isinstance(val, (P4ComplexType, deque)):
                result.__dict__[name] = copy(val)
        return result




class Header(P4ComplexType):

    def __init__(self, z3_reg, z3_type, name):
        self.valid = z3.Bool(f"{name}_valid")
        super(Header, self).__init__(z3_reg, z3_type, name)

    def set_list(self, rval):
        self.valid = z3.BoolVal(True)
        for index, val in enumerate(rval):
            accessor = self.accessors[index]
            self.set_or_add_var(accessor.name(), val)
        return

    def isValid(self, *args):
        # This is a built-in
        return self.valid

    def setValid(self, p4_state):
        # This is a built-in
        self.valid = z3.BoolVal(True)
        return p4_state.get_z3_repr()

    def setInvalid(self, p4_state):
        # This is a built-in
        self.valid = z3.BoolVal(False)
        return p4_state.get_z3_repr()

    def __eq__(self, other):
        if isinstance(other, Header):
            # correspond to the P4 semantics for comparing headers
            # when both headers are invalid return true
            check_invalid = z3.And(z3.Not(self.isValid()),
                                   z3.Not(other.isValid()))
            # when both headers are valid compare the values
            check_valid = z3.And(self.isValid(), other.isValid())
            self_const = self.get_z3_repr()
            other_const = other.get_z3_repr()
            comparison = z3.And(check_valid, self_const == other_const)
            return z3.Or(check_invalid, comparison)
        return super().__eq__(other)


class HeaderUnion(P4ComplexType):
    # TODO: Implement this class correctly...

    def __init__(self, z3_reg, z3_type, name):
        self.valid = z3.Bool(f"{name}_valid")
        super(HeaderUnion, self).__init__(z3_reg, z3_type, name)

    def set_list(self, rval):
        self.valid = z3.BoolVal(True)
        for index, val in enumerate(rval):
            accessor = self.accessors[index]
            self.set_or_add_var(accessor.name(), val)
        return

    def isValid(self, *args):
        # This is a built-in
        return self.valid

    def setValid(self, p4_state):
        # This is a built-in
        self.valid = z3.BoolVal(True)
        return p4_state.get_z3_repr()

    def setInvalid(self, p4_state):
        # This is a built-in
        self.valid = z3.BoolVal(False)
        return p4_state.get_z3_repr()

class HeaderStack(P4ComplexType):

    def __init__(self, z3_reg, z3_type, name):
        super(HeaderStack, self).__init__(z3_reg, z3_type, name)
        self.size = len(self.accessors)

    def push_front(self, p4_state, num):
        # This is a built-in
        for hdr_idx in range(num):
            hdr = self.get_var(f"{hdr_idx}")
            if hdr:
                hdr.valid = z3.BoolVal(True)
        return step(p4_state)

    def pop_front(self, p4_state, num):
        # This is a built-in
        for hdr_idx in range(num):
            hdr = self.get_var(f"{hdr_idx}")
            if hdr:
                hdr.valid = z3.BoolVal(False)
        return step(p4_state)


class Struct(P4ComplexType):

    def set_list(self, rval):
        for index, val in enumerate(rval):
            accessor = self.accessors[index]
            self.set_or_add_var(accessor.name(), val)
        return


class Enum(P4ComplexType):

    def __init__(self, z3_reg, z3_type: z3.SortRef, name):
        super(Enum, self).__init__(z3_reg, z3_type, name)
        # self.name = name
        # self.z3_type = z3_type
        # self.const = z3.Const(f"{self.name}", z3_type)
        # self.constructor = z3_type.constructor(0)
        # These are special for enums
        self._set_z3_accessors(z3_type, self.constructor)
        self._init_members(z3_reg, None, self.accessors)

    def _set_z3_accessors(self, z3_type, constructor):
        self.accessors = []
        for type_index in range(constructor.arity()):
            accessor = z3_type.accessor(0, type_index)
            self.accessors.append(accessor)

    def _init_members(self, z3_reg, const, accessors):
        # Instead of a z3 variable we assign a concrete number to each member
        for idx, accessor in enumerate(accessors):
            setattr(self, accessor.name(), z3.BitVecVal(idx, 8))

    def propagate_type(self, parent_const: z3.AstRef):
        # Enums are static so they do not have variable types.
        pass

    def __eq__(self, other):
        if isinstance(other, z3.ExprRef):
            # if we compare to a z3 expression we are free to chose the value
            # it does not matter if we are out of range, this just means false
            # with this we can generate an interpretable type
            # TODO: Should the type differ per invocation?
            z3_type = other.sort()
            return z3.Const(self.name, z3_type) == other
        else:
            return z3.BoolVal(False)


class P4State(P4ComplexType):
    """
    A P4State Object is a special, dynamic type of P4ComplexType. It represents
    the execution environment and its z3 representation is ultimately used to
    compare different programs. P4State is mostly just a wrapper for all inout
    values. It also manages the execution chain of the program.
    """

    def __init__(self, z3_reg, z3_type, name):
        # deques allow for much more efficient pop and append operations
        # this is all we do so this works well
        super(P4State, self).__init__(z3_reg, z3_type, name)
        self.expr_chain = deque()

    def _update(self):
        self.const = z3.Const(f"{self.name}_1", self.z3_type)

    def set_or_add_var(self, lstring, rval):
        P4ComplexType.set_or_add_var(self, lstring, rval)
        self._update()

    def add_globals(self, globals):
        for extern_name, extern_method in globals.items():
            self.set_or_add_var(extern_name, extern_method)

    def clear_expr_chain(self):
        self.expr_chain.clear()

    def copy_expr_chain(self):
        return self.expr_chain.copy()

    def set_expr_chain(self, expr_chain):
        self.expr_chain = deque(expr_chain)

    def insert_exprs(self, exprs):
        if isinstance(exprs, list):
            self.expr_chain.extendleft(reversed(exprs))
        else:
            self.expr_chain.appendleft(exprs)

class Z3Reg():
    def __init__(self):
        self._types = {}
        self._globals = {}
        self._classes = {}
        self._ref_count = {}

    def _register_structlike(self, name, p4_class, z3_args):
        self._types[name] = z3.Datatype(name)
        self._types[name].declare(f"mk_{name}", *z3_args)
        self._types[name] = self._types[name].create()
        self._classes[name] = p4_class
        self._ref_count[name] = 0

    def declare_global(self, type_str, name, global_val):
        type_str = type_str.lower()
        if type_str == "header":
            self._register_structlike(name, Header, global_val)
        elif type_str == "struct":
            self._register_structlike(name, Struct, global_val)
        elif type_str == "stack":
            self._register_structlike(name, HeaderStack, global_val)
        elif type_str == "enum":
            # Enums are a bit weird... we first create a type
            enum_types = []
            for enum_name in global_val:
                enum_types.append((enum_name, z3.BitVecSort(8)))
            self._register_structlike(name, Enum, enum_types)
            # And then actually instantiate it so we can reference it later
            self._globals[name] = self.instance(name, self._types[name])
        elif type_str == "typedef":
            self._types[name] = global_val
            self._classes[name] = global_val
            self._ref_count[name] = 0
        elif type_str == "extern":
            # Extern also serve as types, so we need to register them too
            self._types[name] = global_val
            self._globals[name] = global_val
        else:
            self._globals[name] = global_val
            self._types[name] = global_val

    def init_p4_state(self, name, p4_params):
        stripped_args = []
        instances = {}
        for param_name, param in p4_params.items():
            is_ref = param[0]
            param_type = param[1]
            if is_ref == "inout" or is_ref == "out":
                # only inouts or outs matter as output
                stripped_args.append((param_name, param_type))
            else:
                # for inputs we can instantiate something
                instance = self.instance(param_name, param_type)
                instances[param_name] = instance
        self._register_structlike(name, P4State, stripped_args)
        p4_state = self.instance(name, self.type(name))
        p4_state.add_globals(self._globals)
        for instance_name, instance_val in instances.items():
            p4_state.set_or_add_var(instance_name, instance_val)
        return p4_state

    def reset(self):
        self._types.clear()
        self._classes.clear()
        self._ref_count.clear()

    def type(self, type_name):
        if type_name in self._types:
            return self._types[type_name]
        else:
            # lets be bold here and assume that a type that is not known
            # is a generic and can be declared as a generic sort
            val = z3.DeclareSort(type_name)
            self.declare_global("typedef", type_name, val)

    def stack(self, z3_type, num):
        type_name = str(z3_type)
        z3_name = f"{type_name}{num}"
        stack_args = []
        for val in range(num):
            stack_args.append((f"{val}", z3_type))
        self.declare_global("stack", z3_name, stack_args)
        return self.type(z3_name)

    def extern(self, extern_name):
        return self._globals[extern_name]

    def instance(self, var_name, p4z3_type: z3.SortRef):
        if isinstance(p4z3_type, z3.DatatypeSortRef):
            type_name = str(p4z3_type)
            if not var_name:
                var_name = f"{type_name}_{self._ref_count[type_name]}"
            z3_cls = self._classes[type_name]
            self._ref_count[type_name] += 1
            instance = z3_cls(self, p4z3_type, var_name)
            return instance
        elif isinstance(p4z3_type, z3.SortRef):
            return z3.Const(f"{var_name}", p4z3_type)
        else:
            return p4z3_type
