from collections import deque, OrderedDict
from dataclasses import dataclass
import types
import copy
import logging
import z3
from z3int import Z3Int

log = logging.getLogger(__name__)


def gen_instance(context, var_name, p4z3_type):
    p4z3_type = resolve_type(context, p4z3_type)
    if isinstance(p4z3_type, P4ComplexType):
        z3_cls = p4z3_type.instantiate(var_name)
        # this instance is fresh, so bind to itself
        z3_cls.bind(z3_cls.const)
        return z3_cls
    elif isinstance(p4z3_type, P4ComplexInstance):
        # static complex type, just return
        return p4z3_type
    elif isinstance(p4z3_type, z3.SortRef):
        return z3.Const(var_name, p4z3_type)
    elif isinstance(p4z3_type, list):
        instantiated_list = []
        for idx, z3_type in enumerate(p4z3_type):
            const = z3.Const(f"{var_name}_{idx}", z3_type)
            instantiated_list.append(const)
        return instantiated_list
    raise RuntimeError(f"{p4z3_type} instantiation not supported!")


def z3_cast(val, to_type):

    # some checks to guarantee that the inputs are usable
    if isinstance(val, (z3.BoolSortRef, z3.BoolRef)):
        # Convert boolean variables to a bit vector representation
        # TODO: Streamline bools and their evaluation
        val = z3.If(val, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

    if isinstance(to_type, (z3.BoolSortRef, z3.BoolRef)):
        # casting to a bool is simple, just check if the value is equal to 1
        # this works for bitvectors and integers, we convert any bools before
        # if val is not a single bit vector, this will (intentionally) fail
        return val == z3.BitVecVal(1, 1)

    # from here on we assume we are working with integer or bitvector types
    if isinstance(to_type, (z3.BitVecSortRef, z3.BitVecRef)):
        # It can happen that we get a bitvector type as target, get its size.
        to_type_size = to_type.size()
    else:
        to_type_size = to_type

    if isinstance(val, int):
        # It can happen that we get an int, cast it to a bit vector.
        return z3.BitVecVal(val, to_type_size)

    # preprocessing done, the actual casting starts here
    val_size = val.size()
    if val_size < to_type_size:
        # the target value is larger, extend with zeros
        return z3.ZeroExt(to_type_size - val_size, val)
    elif val_size > to_type_size:
        # the target value is smaller, truncate everything on the right
        return z3.Extract(to_type_size - 1, 0, val)
    else:
        # nothing to do
        return val


def merge_attrs(target_cls, cond, then_attrs):
    for then_name, then_val in then_attrs.items():
        try:
            attr_val = target_cls.resolve_reference(then_name)
        except RuntimeError:
            # if the attribute does not exist it is not relevant
            # this is because of scoping
            # FIXME: Make sure this is actually the case...
            continue
        if isinstance(attr_val, P4ComplexInstance):
            attr_val.valid = z3.simplify(
                z3.If(cond, then_val.valid, attr_val.valid))
            merge_attrs(attr_val, cond, then_val.locals)
        elif isinstance(attr_val, z3.ExprRef):
            if then_val.sort() != attr_val.sort():
                attr_val = z3_cast(attr_val, then_val.sort())
            if_expr = z3.simplify(z3.If(cond, then_val, attr_val))
            target_cls.set_or_add_var(then_name, if_expr)


def mux_merge(cond, target, else_attrs):
    for idx, (member_name, _) in enumerate(target.members):
        then_val = target.resolve_reference(member_name)
        else_val = else_attrs[idx]
        if isinstance(then_val, P4ComplexInstance):
            mux_merge(cond, then_val, else_val)
        else:
            if_expr = z3.If(cond, then_val, else_val)
            target.set_or_add_var(member_name, if_expr)


def handle_mux(cond, then_expr, else_expr):
    # TODO: Simplify this

    # we may return complex types, we have to unroll these
    if isinstance(then_expr, P4ComplexInstance):
        # record the validity
        then_valid = then_expr.valid
        # if the else expression is complex, we grab a list of the members
        if isinstance(else_expr, P4ComplexInstance):
            else_valid = else_expr.valid
            members = []
            for member_name, _ in else_expr.members:
                members.append(else_expr.resolve_reference(member_name))
            else_expr = members
        # if we have a list initializer, it will make the target value valid
        elif isinstance(else_expr, list):
            else_valid = z3.BoolVal(True)
        else:
            RuntimeError(f"Complex merge not supported for {else_expr}!")
        # start to merge the variables
        mux_merge(cond, then_expr, else_expr)
        # merge the validity of the return expressions
        propagate_validity_bit(then_expr, z3.If(cond, then_valid, else_valid))
        return then_expr

    # repeat the same check if the else expression is complex
    if isinstance(else_expr, P4ComplexInstance):
        # record the validity
        else_valid = else_expr.valid
        # if the else expression is complex, we grab a list of the members
        if isinstance(then_expr, P4ComplexInstance):
            then_valid = then_expr.valid
            members = []
            for member_name, _ in then_expr.members:
                members.append(then_expr.resolve_reference(member_name))
            then_expr = members
        # if we have a list initializer, it will make the target value valid
        elif isinstance(then_expr, list):
            then_valid = z3.BoolVal(True)
        else:
            RuntimeError(f"Complex merge not supported for {then_expr}!")
        # start to merge the variables
        mux_merge(cond, else_expr, then_expr)
        # merge the validity of the return expressions
        propagate_validity_bit(else_expr, z3.If(cond, else_valid, then_valid))
        return else_expr

    # we have to return a nested list when dealing with two lists
    if isinstance(then_expr, list) and isinstance(else_expr, list):
        def list_merge(then_list, else_list):
            merged_list = []
            for idx, then_val in enumerate(then_list):
                else_val = else_list[idx]
                if isinstance(then_val, list):
                    # note how we append, we do not extend
                    # we want to maintain the nesting structure
                    merged_list.append(list_merge(then_val, else_val))
                else:
                    merged_list.append(z3.If(cond, then_val, else_val))
            return merged_list
        merged_list = list_merge(then_expr, else_expr)
        return merged_list

    # assume normal z3 types at this point
    # this will fail if there is an unexpected input
    return z3.If(cond, then_expr, else_expr)


def propagate_validity_bit(target, parent_valid=None):
    if isinstance(target, HeaderInstance) and parent_valid is None:
        parent_valid = z3.Bool(f"{target.name}_valid")
    if parent_valid is not None:
        target.valid = parent_valid
    # structs can be contained in headers so they can also be deactivated...
    for member_name, _ in target.members:
        member_val = target.resolve_reference(member_name)
        if isinstance(member_val, P4ComplexInstance):
            propagate_validity_bit(member_val, parent_valid)


def check_validity(target, parent_validity=None):
    if parent_validity is None:
        if isinstance(target, HeaderInstance):
            parent_validity = target.valid
    for member_name, member_type in target.members:
        # retrieve the member we are accessing
        member = target.resolve_reference(member_name)
        if isinstance(member, P4ComplexInstance):
            # it is a complex type
            # propagate the validity to all children
            check_validity(member, parent_validity)
        else:
            if parent_validity is None:
                continue
            # if the header is invalid set the variable to "undefined"
            cond = z3.simplify(z3.If(parent_validity, member,
                                     z3.Const("invalid", member_type)))
            target.set_or_add_var(member_name, cond)


def resolve_type(context, p4_type):
    if isinstance(p4_type, str):
        try:
            p4_type = context.get_type(p4_type)
        except KeyError:
            p4_type = None

    if isinstance(p4_type, TypeSpecializer):
        p4_type = p4_type.eval(context)
    return p4_type


@dataclass
class P4Parameter:
    __slots__ = ["is_ref", "name", "p4_type", "p4_default"]
    is_ref: str
    name: str
    p4_type: object
    p4_default: object


@dataclass
class P4Argument:
    __slots__ = ["is_ref", "p4_type", "p4_val"]
    is_ref: str
    p4_type: object
    p4_val: object


@dataclass
class Member:
    __slots__ = ["name", "p4_type", "width"]
    name: str
    p4_type: object
    width: int


class P4Z3Class():

    def eval(self, p4_state):
        raise NotImplementedError("Method eval not implemented!")



class P4Expression(P4Z3Class):
    def eval(self, p4_state):
        raise NotImplementedError("Method eval not implemented!")


class P4Statement(P4Z3Class):
    def eval(self, p4_state):
        raise NotImplementedError("Method eval not implemented!")


class DefaultExpression(P4Z3Class):
    def __init__(self):
        pass

    def eval(self, p4_state):
        pass


class P4Range(P4Z3Class):
    def __init__(self, range_min, range_max):
        self.min = range_min
        self.max = range_max

    def eval(self, p4_state):
        pass


class P4Declaration(P4Statement):
    # the difference between a P4Declaration and a ValueDeclaration is that
    # we resolve the variable in the ValueDeclaration
    # in the declaration we assign variables as is.
    # they are resolved at runtime by other classes
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def compute_rval(self, p4_state):
        return self.rval

    def eval(self, p4_state):
        p4_state.set_or_add_var(self.lval, self.compute_rval(p4_state), True)


class ValueDeclaration(P4Declaration):
    def __init__(self, lval, rval, z3_type=None):
        super(ValueDeclaration, self).__init__(lval, rval)
        self.z3_type = z3_type

    def compute_rval(self, p4_state):
        # this will only resolve expressions no other classes
        # FIXME: Untangle this a bit
        z3_type = resolve_type(p4_state, self.z3_type)
        if self.rval is not None:
            rval = p4_state.resolve_expr(self.rval)
            if isinstance(rval, int):
                if isinstance(z3_type, (z3.BitVecSortRef)):
                    rval = z3_cast(rval, z3_type)
            elif isinstance(rval, list):
                instance = gen_instance(p4_state, "undefined", z3_type)
                instance.set_list(rval)
                rval = instance
            elif z3_type != rval.sort():
                msg = f"There was an problem setting {self.lval} to {rval}. " \
                    f"Type Mismatch! Target type {z3_type} " \
                    f"does not match with input type {rval.sort()}"
                raise RuntimeError(msg)
        else:
            rval = gen_instance(p4_state, "undefined", z3_type)
        return rval


class ControlDeclaration(P4Z3Class):
    # this is a wrapper to deal with the fact that P4Controls can be both types
    # and accessible variables for some reason
    def __init__(self, ctrl):
        self.ctrl = ctrl


class TypeDeclaration(P4Z3Class):
    # this is a wrapper to deal with the fact that P4Controls can be both types
    # and accessible variables for some reason
    def __init__(self, name, p4_type):
        self.name = name
        self.p4_type = p4_type


class TypeSpecializer():
    def __init__(self, p4z3_type, *args):
        self.p4z3_type = p4z3_type
        self.args = args

    def eval(self, context):
        p4z3_type = resolve_type(context, self.p4z3_type)
        return p4z3_type.init_type_params(context, *self.args)


class InstanceDeclaration(ValueDeclaration):
    def __init__(self, lval, p4z3_type, *args, **kwargs):
        super(InstanceDeclaration, self).__init__(lval, p4z3_type)
        self.args = args
        self.kwargs = kwargs

    def compute_rval(self, context):
        z3_type = resolve_type(context, self.rval)
        z3_type = z3_type.initialize(context, *self.args, **self.kwargs)
        return z3_type

    def eval(self, p4_state):
        p4_state.set_or_add_var(self.lval, self.compute_rval(p4_state), True)


class P4Member(P4Expression):

    __slots__ = ["lval", "member"]

    def __init__(self, lval, member):
        self.lval = lval
        self.member = member

    def eval(self, context):
        if isinstance(self.lval, P4Index):
            return self.lval.eval(context, self.member)
        lval = context.resolve_expr(self.lval)
        return lval.locals[self.member]

    def set_value(self, context, rval):
        if isinstance(self.lval, P4Index):
            self.lval.set_value(context, rval, self.member)
            return
        target = context.resolve_reference(self.lval)
        target.set_or_add_var(self.member, rval)

    def __repr__(self):
        return f"{self.lval}.{self.member}"


class P4Index(P4Member):
    # FIXME: This class is an absolute nightmare. Fix
    __slots__ = ["lval", "member"]

    def eval(self, context, target_member=None):
        lval = context.resolve_expr(self.lval)
        index = context.resolve_expr(self.member)
        if isinstance(index, z3.ExprRef):
            index = z3.simplify(index)
        if isinstance(index, int):
            index = str(index)
        elif isinstance(index, z3.BitVecNumRef):
            index = str(index.as_long())
        elif isinstance(index, z3.BitVecRef):
            if target_member:
                max_idx = lval.locals["size"]
                return_expr = lval.locals[str(
                    0)].resolve_reference(target_member)
                for hdr_idx in range(1, max_idx):
                    cond = index == hdr_idx
                    val = lval.locals[f"{hdr_idx}"].resolve_reference(
                        target_member)
                    return_expr = handle_mux(cond, val, return_expr)
                return return_expr
            else:
                max_idx = lval.locals["size"]
                return_expr = lval.locals[f"0"]
                for hdr_idx in range(1, max_idx):
                    cond = index == hdr_idx
                    return_expr = handle_mux(
                        cond, lval.locals[f"{hdr_idx}"], return_expr)
                return return_expr
        else:
            raise RuntimeError(f"Unsupported index {type(index)}!")
        if target_member:
            return lval.locals[index].resolve_reference(target_member)
        else:
            return lval.locals[index]

    def set_value(self, context, rval, target_member=None):
        lval = context.resolve_expr(self.lval)
        index = context.resolve_expr(self.member)
        if isinstance(index, z3.ExprRef):
            index = z3.simplify(index)
        if isinstance(index, int):
            index = str(index)
        elif isinstance(index, z3.BitVecNumRef):
            index = str(index.as_long())
        elif isinstance(index, z3.BitVecRef):
            if target_member:
                max_idx = lval.locals["size"]
                for hdr_idx in range(max_idx):
                    hdr = lval.locals[f"{hdr_idx}"]
                    cond = index == hdr_idx
                    cur_val = hdr.resolve_reference(target_member)
                    if_expr = z3.If(cond, rval, cur_val)
                    hdr.set_or_add_var(target_member, if_expr)
            else:
                max_idx = lval.locals["size"]
                for hdr_idx in range(1, max_idx):
                    cond = index == hdr_idx
                    mux_expr = handle_mux(cond, rval,
                                          context.locals[f"{hdr_idx}"])
                    lval.set_or_add_var(hdr_idx, mux_expr)
            return
        else:
            raise RuntimeError(f"Unsupported index {type(index)}!")

        if target_member:
            hdr = lval.locals[f"{index}"]
            hdr.set_or_add_var(target_member, rval)
        else:
            lval.set_or_add_var(index, rval)


class P4Slice(P4Expression):
    def __init__(self, val, slice_l, slice_r):
        self.val = val
        self.slice_l = slice_l
        self.slice_r = slice_r

    def eval(self, p4_state):
        val = p4_state.resolve_expr(self.val)
        slice_l = p4_state.resolve_expr(self.slice_l)
        slice_r = p4_state.resolve_expr(self.slice_r)

        if isinstance(val, int):
            val = val.as_bitvec
        return z3.Extract(slice_l, slice_r, val)


class P4ComplexType():
    """ A P4ComplexType is a wrapper for any type that is not a simple Z3 type
    such as IntSort, BitVecSort or BoolSort.
    A P4ComplexType creates an P4ComplexInstance , all subtypes
    become members of this class and be accessed in dot-notation
    (e.g., headers.eth.srcmac).
    If one of the children is a P4ComplexType a new P4ComplexInstance will be
    instantiated and attached as member.
    Every member of this class should either be a P4ComplexType or a z3.SortRef
     if it is a basic type. A DataTypeRef should never be a member and always
    needs to be converted to a P4ComplexType.
    """

    def __init__(self, name):
        self.name = name
        self.z3_type = None

    def instantiate(self, name, member_id=0):
        return P4ComplexInstance(name, self, member_id)

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        # lets us compare different z3 types with each other
        # needed for type checking
        if isinstance(other, P4ComplexType):
            return self.z3_type == other.z3_type
        elif isinstance(other, z3.AstRef):
            return self.z3_type == other
        return super(P4ComplexType).__eq__(other)


class P4ComplexInstance():
    def __init__(self, name, p4z3_type, member_id):
        self.locals = {}
        self.name = name
        self.z3_type = p4z3_type.z3_type
        self.width = p4z3_type.width
        self.p4z3_type = p4z3_type
        self.member_id = member_id
        self.members = p4z3_type.z3_args
        self.valid = z3.BoolVal(False)

    def resolve_reference(self, var):
        if isinstance(var, P4Member):
            return var.eval(self)
        if isinstance(var, str):
            return self.locals[var]
        return var

    def set_list(self, rvals):
        for idx, (member_name, member_type) in enumerate(self.members):
            val = rvals[idx]
            # integers need to be cast to the respective type
            if isinstance(val, int):
                val = z3_cast(val, member_type)
            self.set_or_add_var(member_name, val)
        # whenever we set a list, the target instances becomes valid
        self.valid = z3.BoolVal(True)

    def set_or_add_var(self, lval, rval):
        if isinstance(lval, P4Member):
            lval.set_value(self, rval)
            return
        # rvals could be a list, unroll the assignment
        if isinstance(rval, list) and lval in self.locals:
            lval_val = self.locals[lval]
            if isinstance(lval_val, P4ComplexInstance):
                lval_val.set_list(rval)
            else:
                raise TypeError(
                    f"set_list {type(lval)} not supported!")
            return
        self.locals[lval] = rval

    def sort(self):
        return self.p4z3_type

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result.locals = copy.copy(self.locals)
        for name, val in self.locals.items():
            if isinstance(val, P4ComplexInstance):
                result.locals[name] = copy.copy(val)
        return result

    def __repr__(self):
        return f"{self.__class__.__name__}"

    def __eq__(self, other):
        # It can happen that we compare to a list
        # comparisons are almost the same just do not use members
        if isinstance(other, P4ComplexInstance):
            other_list = []
            for other_member_name, _ in other.members:
                other_list.append(other.resolve_reference(other_member_name))
        elif isinstance(other, list):
            other_list = other
        else:
            return z3.BoolVal(False)

        # there is a mismatch in members, clearly not equal
        if len(self.members) != len(other_list):
            return z3.BoolVal(False)

        eq_members = []
        for index, (self_member_name, _) in enumerate(self.members):
            self_member = self.resolve_reference(self_member_name)
            other_member = other_list[index]
            # we compare the members of each complex type
            z3_eq = self_member == other_member
            eq_members.append(z3_eq)
        return z3.And(*eq_members)


class StructType(P4ComplexType):

    def __init__(self, name, z3_reg, z3_args):
        super(StructType, self).__init__(name)
        flat_names = []
        self.width = 0
        self.z3_reg = z3_reg
        self.z3_args = z3_args

        for idx, (member_name, member_type) in enumerate(z3_args):
            member_type = resolve_type(z3_reg, member_type)
            if isinstance(member_type, P4ComplexType):
                # the member is a complex type
                # retrieve it is flat list of members
                # append it to the member list
                for sub_member in member_type.flat_names:
                    member = Member(P4Member(member_name, sub_member.name),
                                    sub_member.p4_type,
                                    sub_member.width)
                    flat_names.append(member)
                self.width += member_type.width
            else:
                if isinstance(member_type, z3.BoolSortRef):
                    # bools do not have a size attribute unfortunately
                    member_width = 1
                elif isinstance(member_type, z3.BitVecSortRef):
                    member_width = member_type.size()
                else:
                    # a kind of strange sub-type, unclear what its width is
                    # example: generics
                    member_width = 0
                self.width += member_width
                member = Member(member_name, member_type, member_width)
                flat_names.append(member)
            self.z3_args[idx] = (member_name, member_type)

        if self.width == 0:
            # we are dealing with an empty struct, create a dummy datatype
            z3_type = z3.Datatype(name)
            z3_type.declare(f"mk_{name}")
            self.z3_type = z3_type.create()
        else:
            # use the flat bit width of the struct as datatype
            self.z3_type = z3.BitVecSort(self.width)
        self.flat_names = flat_names

    def instantiate(self, name, member_id=0):
        return StructInstance(name, self, member_id)


class StructInstance(P4ComplexInstance):

    def __init__(self, name, p4z3_type, member_id):
        super(StructInstance, self).__init__(name, p4z3_type, member_id)
        self.const = z3.Const(name, self.z3_type)

        # we use the overall index of the struct for a uniform naming scheme
        flat_idx = self.member_id
        for member_name, member_type in self.members:

            if isinstance(member_type, P4ComplexType):
                # the z3 variable of the instance is only an id
                instance = member_type.instantiate(str(flat_idx), flat_idx)
                # but what we add is its fully qualified name, e.g. x.y.z
                self.locals[member_name] = instance
                flat_idx += len(member_type.flat_names)
            else:
                # this is just a filler value, it must be overridden by bind()
                self.locals[member_name] = None
                flat_idx += 1

    def bind(self, bind_const):
        # the identification of the member starts with the provided member id
        # this bit_width must sum up to the bit width of the sub members
        bit_width = self.width
        # set the members of this class
        for sub_member in self.p4z3_type.flat_names:
            # we bind by extracting the respective bit range
            bind_var = z3.Extract(bit_width - 1,
                                  bit_width - sub_member.width, bind_const)
            if isinstance(sub_member.p4_type, z3.BoolSortRef):
                # unfortunately bools still exit, we need to cast them
                bind_var = z3_cast(bind_var, sub_member.p4_type)
            # set the new bind value
            self.set_or_add_var(sub_member.name, bind_var)
            bit_width -= sub_member.width

    def activate(self, label="undefined"):
        # structs may contain headers that can be deactivated
        for member_name, _ in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.activate()

    def deactivate(self, label="undefined"):
        # structs may contain headers that can be deactivated
        for member_name, _ in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.deactivate(label)

    def flatten(self):
        members = []
        for member_name, _ in self.members:
            member = self.resolve_reference(member_name)
            if isinstance(member, P4ComplexInstance):
                sub_members = member.flatten()
                members.extend(sub_members)
            else:
                members.append(member)
        return members


class HeaderType(StructType):

    def instantiate(self, name, member_id=0):
        return HeaderInstance(name, self, member_id)


class HeaderInstance(StructInstance):

    def __init__(self, name, p4z3_type, member_id):
        super(HeaderInstance, self).__init__(name, p4z3_type, member_id)
        self.valid = z3.BoolVal(False)
        self.locals["isValid"] = self.isValid
        self.locals["setValid"] = self.setValid
        self.locals["setInvalid"] = self.setInvalid
        self.union_parent = None

    def activate(self, label="undefined"):
        for member_name, _ in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.activate()
            else:
                # only if the header was invalid, reallocate all variables
                if self.valid == z3.BoolVal(False):
                    allocated_var = z3.Const(label, member_val.sort())
                    self.set_or_add_var(member_name, allocated_var)
        self.valid = z3.BoolVal(True)

    def deactivate(self, label="undefined"):
        for member_name, member_type in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.deactivate(label)
            else:
                member_const = z3.Const(label, member_type)
                self.set_or_add_var(member_name, member_const)
        self.valid = z3.BoolVal(False)

    def isValid(self, p4_state=None):
        # This is a built-in
        return self.valid

    def setValid(self, p4_state):
        if self.union_parent:
            # this is a hacky way to invalidate other members
            # in the case that this header is part of a union
            union = self.union_parent
            for member_name, _ in union.members:
                member_hdr = union.resolve_reference(member_name)
                # check whether the header is the same object
                # any other header is now invalid
                if member_hdr is not self:
                    member_hdr.setInvalid(p4_state)
        # This is a built-in
        self.activate()

    def setInvalid(self, p4_state):
        if self.union_parent:
            # this is a hacky way to invalidate other members
            # in the case that this header is part of a union
            union = self.union_parent
            for member_name, _ in union.members:
                member_hdr = union.resolve_reference(member_name)
                # check whether the header is the same object
                # any other header is now invalid
                member_hdr.deactivate()
        # This is a built-in
        self.deactivate()

    def bind_to_union(self, union_instance):
        # FIXME: This ignores copying
        # the reference in the parent will be stale
        # this works only because we merge all the variables, including parents
        self.union_parent = union_instance

    def __eq__(self, other):
        if isinstance(other, HeaderInstance):
            # correspond to the P4 semantics for comparing headers
            # when both headers are invalid return true
            check_invalid = z3.And(z3.Not(self.isValid()),
                                   z3.Not(other.isValid()))
            # when both headers are valid compare the values
            check_valid = z3.And(self.isValid(), other.isValid())

            self_const = self.flatten()
            other_const = other.flatten()
            comps = []
            for idx, self_val in enumerate(self_const):
                comps.append(self_val == other_const[idx])
            comparison = z3.And(check_valid, *comps)
            return z3.simplify(z3.Or(check_invalid, comparison))
        return super().__eq__(other)

    def __copy__(self):
        result = super(HeaderInstance, self).__copy__()
        # we need to update the reference of the function to the new object
        # quite nasty...
        result.locals["isValid"] = result.isValid
        result.locals["setValid"] = result.setValid
        result.locals["setInvalid"] = result.setInvalid
        return result


class HeaderUnionType(StructType):
    def instantiate(self, name, member_id=0):
        return HeaderUnionInstance(name, self, member_id)


class HeaderUnionInstance(StructInstance):

    def __init__(self, name, p4z3_type, member_id):
        # TODO: Check if this class is implemented correctly...
        super(HeaderUnionInstance, self).__init__(name, p4z3_type, member_id)
        for member_name, _ in self.members:
            member_hdr = self.resolve_reference(member_name)
            member_hdr.bind_to_union(self)
        self.locals["isValid"] = self.isValid

    @property
    def valid(self):
        valid_list = []
        for member_name, _ in self.members:
            member_hdr = self.resolve_reference(member_name)
            valid_list.append(member_hdr.isValid())
        return z3.simplify(z3.Or(*valid_list))

    def isValid(self, p4_state=None):
        # This is a built-in
        return self.valid

    def __setattr__(self, name, val):
        # FIXME: Fix this workaround for valid attributes
        if name == "valid":
            # do not override the custom valid computation here
            # header union validity is dependent on its members
            pass
        else:
            self.__dict__[name] = val

    def __copy__(self):
        result = super(HeaderUnionInstance, self).__copy__()
        # we need to update the reference of the function to the new object
        # quite nasty...
        result.locals["isValid"] = result.isValid
        return result


class ListType(StructType):

    def __init__(self, name, z3_reg, z3_args):
        for idx, arg in enumerate(z3_args):
            z3_args[idx] = (f"{idx}", arg)
            # some little hack to automatically infer a random type name
            name += str(arg)
        super(ListType, self).__init__(name, z3_reg, z3_args)

    # TODO: Implement this class correctly...
    def instantiate(self, name, member_id=0):
        return ListInstance(name, self, member_id)


class ListInstance(StructInstance):
    pass


class HeaderStack(StructType):

    def __init__(self, name, z3_reg, z3_args):
        for idx, arg in enumerate(z3_args):
            z3_args[idx] = (f"{idx}", arg)
        super(HeaderStack, self).__init__(name, z3_reg, z3_args)

    # TODO: Implement this class correctly...
    def instantiate(self, name, member_id=0):
        return HeaderStackInstance(name, self, member_id)


class HeaderStackDict(dict):
    def __init__(self, init_dict, parent_hdr):
        self.parent_hdr = parent_hdr
        dict.__init__(self)
        for key, val in init_dict.items():
            dict.__setitem__(self, key, val)

    def __getitem__(self, key):
        if key == "next":
            # This is a built-in
            # TODO: Check if this implementation makes sense
            try:
                hdr = self.parent_hdr.locals[f"{self.parent_hdr.nextIndex}"]
            except KeyError:
                # if the header does not exist use it to break out of the loop?
                size = self.parent_hdr.locals["size"]
                hdr = self.parent_hdr.locals[f"{size -1}"]
            self.parent_hdr.nextIndex += 1
            self.parent_hdr.locals["lastIndex"] += 1
            return hdr
        if key == "last":
            # This is a built-in
            # TODO: Check if this implementation makes sense
            last = 0 if self.parent_hdr.locals["size"] < 1 else self.parent_hdr.locals["size"] - 1
            hdr = self.parent_hdr.locals[f"{last}"]
            return hdr

        val = dict.__getitem__(self, key)
        return val

    def __setitem__(self, key, val):
        dict.__setitem__(self, key, val)


class HeaderStackInstance(StructInstance):

    def __init__(self, name, p4z3_type, member_id):
        super(HeaderStackInstance, self).__init__(name, p4z3_type, member_id)

        # this is completely nuts but it works for now
        # no idea how to deal with properties
        # this intercepts dictionary lookups and modifies the header in place
        self.locals = HeaderStackDict(self.locals, self)
        self.nextIndex = 0
        self.locals["push_front"] = self.push_front
        self.locals["pop_front"] = self.pop_front
        self.locals["size"] = len(self.members)
        self.locals["lastIndex"] = len(self.members) - 1

    def push_front(self, p4_state, num):
        # This is a built-in
        # TODO: Check if this implementation makes sense
        for hdr_idx in range(1, num):
            hdr_idx = hdr_idx - 1
            try:
                hdr = self.locals[f"{hdr_idx}"]
                hdr.setValid(p4_state)
            except KeyError:
                pass

    def pop_front(self, p4_state, num):
        # This is a built-in
        # TODO: Check if this implementation makes sense
        for hdr_idx in range(1, num):
            hdr_idx = hdr_idx - 1
            try:
                hdr = self.locals[f"{hdr_idx}"]
                hdr.setInvalid(p4_state)
            except KeyError:
                pass

    @property
    def next(self):
        # This is a built-in
        # TODO: Check if this implementation makes sense
        try:
            hdr = self.locals[f"{self.nextIndex}"]
        except KeyError:
            # if the header does not exist use it to break out of the loop?
            size = self.locals["size"]
            hdr = self.locals[f"{size -1}"]
        self.nextIndex += 1
        self.locals["lastIndex"] += 1
        return hdr

    @property
    def last(self):
        # This is a built-in
        # TODO: Check if this implementation makes sense
        last = 0 if self.locals["size"] < 1 else self.locals["size"] - 1
        hdr = self.locals[f"{last}"]
        return hdr

    def __setattr__(self, name, val):
        # TODO: Fix this workaround for next attributes
        if name == "next":
            self.__setattr__(f"{self.nextIndex}", val)
            self.nextIndex += 1
        else:
            self.__dict__[name] = val

    def __copy__(self):
        result = super(HeaderStackInstance, self).__copy__()
        # update references to the method calls
        result.locals["push_front"] = result.push_front
        result.locals["pop_front"] = result.pop_front
        return result


class Enum(P4ComplexInstance):

    def __init__(self, name, z3_args):
        self.locals = {}
        self.name = name
        self.z3_type = z3.BitVecSort(32)
        for idx, enum_name in enumerate(z3_args):
            self.locals[enum_name] = z3.BitVecVal(idx, 32)
        self.z3_args = z3_args

    def instantiate(self, name, member_id=0):
        return self

    def __eq__(self, other):
        if isinstance(other, z3.ExprRef):
            # if we compare to a z3 expression we are free to chose the value
            # it does not matter if we are out of range, this just means false
            # with this we can generate an interpretable type
            # TODO: Should the type differ per invocation?
            z3_type = other.sort()
            return z3.Const(self.name, z3_type) == other
        else:
            log.warning("Enum: Comparison to %s of type %s not supported",
                        other, type(other))
            return z3.BoolVal(False)


class SerEnum(Enum):

    def __init__(self, name, z3_args, z3_type):
        self.arg_vals = []
        self.name = name
        self.z3_type = z3_type
        self.locals = {}
        self.members = z3_args
        for z3_arg_name, z3_arg_val in z3_args:
            self.locals[z3_arg_name] = z3_arg_val

    def instantiate(self, name, member_id=0):
        return self


class P4Extern(P4ComplexInstance):
    def __init__(self, name, type_params=[], methods=[]):
        # Externs are this weird bastard child of callables and a complex type
        # FIXME: Unify types, this is a royal mess
        z3_type = z3.Datatype(name)
        z3_type.declare(f"mk_{name}")
        self.members = []
        self.z3_type = z3_type.create()
        self.p4z3_type = z3_type
        self.const = z3.Const(name, self.z3_type)
        self.locals = {}
        # simple fix for now until I know how to initialize params for externs
        self.params = {}
        self.name = name
        self.type_params = type_params
        # these are method declarations, not methods
        for method in methods:
            self.locals[method.lval] = method.rval
        # dummy
        self.valid = False
        self.type_context = {}

    def init_type_params(self, context, *args, **kwargs):
        # TODO Figure out what to actually do here
        init_extern = copy.copy(self)
        # the type params sometimes include the return type also
        # it is typically the first value, but is bound somewhere else
        for idx, t_param in enumerate(init_extern.type_params):
            arg = resolve_type(context, args[idx])
            init_extern.type_context[t_param] = arg
        for method in init_extern.locals.values():
            method.extern_context = init_extern.type_context
        return init_extern

    def initialize(self, context, *args, **kwargs):
        # FIXME: Try to understand constructor args and what they mean
        # Example: psa-hash.p4
        return self

    def __call__(self, context, *args, **kwargs):
        raise RuntimeError("NO CALLING EXTERNS!")

    def __repr__(self):
        return self.name

    def deactivate(self):
        log.warning("This method should not be called...")

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result.type_params = copy.copy(self.type_params)
        result.locals = {}
        for method_name, method in self.locals.items():
            result.locals[method_name] = copy.copy(method)

        return result


class P4ControlType(P4Extern):
    def __init__(self, name, params, type_params):
        super(P4ControlType, self).__init__(name, type_params, [])
        self.params = params


class P4ParserType(P4ControlType):
    pass


class P4Context(P4Z3Class):

    def __init__(self, var_buffer):
        self.var_buffer = var_buffer
        self.return_states = deque()
        self.has_returned = False
        self.return_exprs = deque()
        self.return_type = None
        self.forward_conds = deque()
        self.tmp_forward_cond = z3.BoolVal(True)
        self.locals = {}

    def add_to_buffer(self, var_dict):
        self.var_buffer = {**self.var_buffer, **var_dict}

    def prepend_to_buffer(self, var_dict):
        self.var_buffer = {**var_dict, **self.var_buffer}

    def declare_var(self, lval, rval):
        self.locals[lval] = rval

    def copy_out(self, p4_state):
        # restore any variables that may have been overridden
        # with copy-out we copy from left to right
        # values on the right override values on the left
        # the var buffer is an ordered dict that maintains this order
        for par_name, (is_ref, par_ref, par_val) in self.var_buffer.items():
            # we retrieve the current value
            val = p4_state.resolve_reference(par_name)

            # we then reset the name in the scope to its original
            log.debug("Resetting %s to %s", par_name, type(par_val))
            # value has not existed previously, ignore
            if par_val is not None:
                p4_state.set_or_add_var(par_name, par_val)

            # if the param was copy-out, we copy the value we retrieved
            # back to the original input reference
            if is_ref in ("inout", "out"):
                log.debug("Copy-out: %s to %s", val, par_ref)
                # copy it back to the input reference
                # this assumes an lvalue as input
                p4_state.set_or_add_var(par_ref, val)


class P4State():
    """
    A P4State Object is a special, dynamic type of P4ComplexType. It represents
    the execution environment and its z3 representation is ultimately used to
    compare different programs. P4State is mostly just a wrapper for all inout
    values. It also manages the execution chain of the program.
    """

    def __init__(self):
        self.name = "init_state"
        self.main_context = P4Context({})
        # deques allow for much more efficient pop and append operations
        # this is all we do so this works well
        self.contexts = deque()
        self.exit_states = deque()
        self.has_exited = False
        self.flat_names = []
        self.members = {}
        self.z3_type = None
        self.const = None
        self.type_map = {}
        self.type_contexts = deque()

    def reset(self):
        self.exit_states = deque()
        self.has_exited = False
        self.contexts = deque()
        self.flat_names = []
        self.z3_type = None
        self.const = None

    def set_datatype(self, name, z3_args, instances):
        self.reset()
        self.name = name
        self.members = z3_args
        state_context = P4Context({})
        self.contexts.append(state_context)

        for instance_name, instance_val in instances.items():
            self.set_or_add_var(instance_name, instance_val)

        flat_args = []
        idx = 0
        for z3_arg_name, z3_arg_type in z3_args:
            z3_arg_type = resolve_type(self, z3_arg_type)
            if isinstance(z3_arg_type, P4ComplexType):
                member_cls = z3_arg_type.instantiate(f"{name}.{idx}")
                propagate_validity_bit(member_cls)
                for sub_member in z3_arg_type.flat_names:
                    flat_args.append((f"{idx}", sub_member.p4_type))
                    self.flat_names.append(
                        P4Member(z3_arg_name, sub_member.name))
                    idx += 1
                # this is a complex datatype, create a P4ComplexType
                self.set_or_add_var(z3_arg_name, member_cls, True)
            else:
                flat_args.append((f"{idx}", z3_arg_type))
                self.flat_names.append(z3_arg_name)
                idx += 1
        z3_type = z3.Datatype(name)
        z3_type.declare(f"mk_{name}", *flat_args)
        self.z3_type = z3_type.create()

        self.const = z3.Const(f"{name}", self.z3_type)

        for type_idx, arg_name in enumerate(self.flat_names):
            member_constructor = self.z3_type.accessor(0, type_idx)
            self.set_or_add_var(arg_name, member_constructor(self.const), True)

    def resolve_expr(self, expr):
        # Resolves to z3 and z3p4 expressions
        # ints, lists, and dicts are also okay

        # resolve potential string references first
        log.debug("Resolving %s", expr)
        if isinstance(expr, str):
            expr = self.resolve_reference(expr)
        if isinstance(expr, P4Expression):
            # We got a P4 expression, recurse and resolve...
            expr = expr.eval(self)
            return self.resolve_expr(expr)
        if isinstance(expr, (z3.AstRef, int)):
            # These are z3 types and can be returned
            # Unfortunately int is part of it because z3 is very inconsistent
            # about var handling...
            return expr
        if isinstance(expr, (P4ComplexInstance, P4Z3Class, types.MethodType)):
            # In a similar manner, just return any remaining class types
            # Methods can be class attributes and need to be returned as is
            return expr
        if isinstance(expr, list):
            # For lists, resolve each value individually and return a new list
            list_expr = []
            for val_expr in expr:
                rval_expr = self.resolve_expr(val_expr)
                list_expr.append(rval_expr)
            return list_expr
        raise TypeError(f"Expression of type {type(expr)} cannot be resolved!")

    def find_nested_slice(self, lval, slice_l, slice_r):
        # gradually reduce the scope until we have calculated the right slice
        # also retrieve the string lvalue in the mean time
        if isinstance(lval, P4Slice):
            lval, _, outer_slice_r = self.find_nested_slice(
                lval.val, lval.slice_l, lval.slice_r)
            slice_l = outer_slice_r + slice_l
            slice_r = outer_slice_r + slice_r
        return lval, slice_l, slice_r

    def set_slice(self, lval, rval):
        slice_l = self.resolve_expr(lval.slice_l)
        slice_r = self.resolve_expr(lval.slice_r)
        lval = lval.val
        lval, slice_l, slice_r = self.find_nested_slice(lval, slice_l, slice_r)

        # need to resolve everything first, these can be members
        lval_expr = self.resolve_expr(lval)

        # z3 requires the extract value to be a bitvector, so we must cast ints
        # actually not sure where this could happen...
        if isinstance(lval_expr, int):
            lval_expr = lval_expr.as_bitvec

        rval_expr = self.resolve_expr(rval)

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

    def find_context(self, var):
        for context in reversed(self.contexts):
            try:
                return context, context.locals[var]
            except KeyError:
                continue
        # nothing found, empty result
        return None, None

    def current_context(self):
        if self.contexts:
            return self.contexts[-1]
        else:
            return self.main_context

    def set_or_add_var(self, lval, rval, new_decl=False):
        if isinstance(lval, P4Slice):
            self.set_slice(lval, rval)
            return
        if isinstance(lval, P4Member):
            lval.set_value(self, rval)
            return
        # now that all the preprocessing is done we can assign the value
        log.debug("Setting %s(%s) to %s(%s) ",
                  lval, type(lval), rval, type(rval))
        context, lval_val = self.find_context(lval)
        if not context or new_decl:
            context = self.contexts[-1]

        # rvals could be a list, unroll the assignment
        if isinstance(rval, list) and lval_val is not None:
            if isinstance(lval_val, P4ComplexInstance):
                lval_val.set_list(rval)
            else:
                raise TypeError(
                    f"set_list {type(lval)} not supported!")
            return
        context.locals[lval] = rval

    def get_z3_repr(self):
        ''' This method returns the current representation of the object in z3
        logic.'''
        members = []
        for member_name, _ in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                # first we need to make sure that validity is correct
                check_validity(member_val)
                members.extend(member_val.flatten())
            else:
                members.append(member_val)
        return self.z3_type.constructor(0)(*members)

    def get_attrs(self):
        attr_dict = {}
        for context in self.contexts:
            for var_name, var_val in context.locals.items():
                attr_dict[var_name] = var_val
        return attr_dict

    def copy_attrs(self):
        attr_copy = {}
        # copy everything except the first context, which are the global values
        for context in self.contexts:
            for attr_name, attr_val in context.locals.items():
                if isinstance(attr_val, P4ComplexInstance):
                    attr_val = copy.copy(attr_val)
                attr_copy[attr_name] = attr_val
        return attr_copy

    def resolve_reference(self, var):
        if isinstance(var, P4Member):
            return var.eval(self)
        if isinstance(var, str):
            context, val = self.find_context(var)
            if not context:
                try:
                    return self.main_context.locals[var]
                except KeyError:
                    raise RuntimeError(f"Variable {var} not found!")
            return val
        return var

    def get_type(self, type_name):
        for context in reversed(self.type_contexts):
            try:
                return context[type_name]
            except KeyError:
                continue
        return self.type_map[type_name]

    def checkpoint(self):
        var_store = self.copy_attrs()
        contexts = self.contexts.copy()
        return var_store, contexts

    def restore(self, var_store, contexts=None):
        for attr_name, attr_val in var_store.items():
            self.set_or_add_var(attr_name, attr_val)
        if contexts:
            self.contexts = contexts


class Z3Reg():
    def __init__(self):
        self.p4_state = P4State()

    def declare_global(self, p4_class):
        if isinstance(p4_class, (P4ComplexType, P4Extern)):
            name = p4_class.name
            self.declare_type(name, p4_class)
        elif isinstance(p4_class, TypeDeclaration):
            p4_type = resolve_type(self, p4_class.p4_type)
            self.declare_type(p4_class.name, p4_type)
        elif isinstance(p4_class, ControlDeclaration):
            self.declare_var(p4_class.ctrl.name, p4_class.ctrl)
            self.declare_type(p4_class.ctrl.name, p4_class.ctrl)
        elif isinstance(p4_class, Enum):
            # enums are special static types
            # we need to add them to the list of accessible variables
            # and their type is actually the z3 type, not the class type
            name = p4_class.name
            self.declare_var(name, p4_class)
            p4_type = resolve_type(self, p4_class.z3_type)
            self.declare_type(name, p4_type)
        elif isinstance(p4_class, P4Declaration):
            name = p4_class.lval
            rval = p4_class.compute_rval(self.p4_state)
            self.declare_var(name, rval)
        else:
            raise RuntimeError(
                "Unsupported global declaration %s" % type(p4_class))

    def resolve_reference(self, var):
        return self.p4_state.resolve_reference(var)

    def resolve_expr(self, var):
        return self.p4_state.resolve_expr(var)

    def declare_var(self, lval, rval):
        self.p4_state.main_context.locals[lval] = rval

    def declare_type(self, lval, rval):
        self.p4_state.type_map[lval] = rval

    def set_p4_state(self, name, p4_params):
        stripped_args = []
        instances = {}
        for param in p4_params:
            if param.is_ref in ("inout", "out"):
                # only inouts or outs matter as output
                stripped_args.append((param.name, param.p4_type))
            else:
                # for other inputs we can instantiate something
                instance = gen_instance(self, param.name, param.p4_type)
                instances[param.name] = instance
        self.p4_state.set_datatype(name, stripped_args, instances)
        return self.p4_state

    def get_type(self, type_name):
        return self.p4_state.type_map[type_name]

    def stack(self, z3_type, num):
        # Header stacks are a bit special because they are basically arrays
        # with specific features
        # We need to declare a new z3 type and add a new complex class
        name = f"{z3_type}{num}"
        p4_stack = HeaderStack(name, self, [z3_type] * num)
        self.declare_global(p4_stack)
        return self.get_type(name)

    def get_value(self, expr):
        val = self.resolve_expr(expr)
        if isinstance(val, z3.BitVecNumRef):
            # unfortunately, we need to get the real int value here
            val = Z3Int(val.as_long(), val.size())
        return val

    def get_main_function(self):
        if "main" in self.p4_state.main_context.locals:
            return self.p4_state.main_context.locals["main"]
        return None
