from dataclasses import dataclass
import copy
import logging
import z3
log = logging.getLogger(__name__)

UNDEF_LABEL = "undefined"


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


def merge_dicts(target_dict, cond, then_attrs):
    for then_name, then_val in then_attrs.items():
        try:
            attr_val = target_dict[then_name]
        except KeyError:
            # if the attribute does not exist it is not relevant
            # this is because of scoping
            # FIXME: Make sure this is actually the case...
            continue
        if isinstance(attr_val, StructInstance):
            attr_val.valid = z3.If(cond, then_val.valid, attr_val.valid)
            merge_attrs(attr_val, cond, then_val.locals)
        elif isinstance(attr_val, z3.ExprRef):
            if then_val.sort() != attr_val.sort():
                attr_val = z3_cast(attr_val, then_val.sort())
            if_expr = z3.If(cond, then_val, attr_val)
            target_dict[then_name] = if_expr


def merge_attrs(target_cls, cond, then_attrs):
    for then_name, then_val in then_attrs.items():
        try:
            attr_val = target_cls.resolve_reference(then_name)
        except KeyError:
            # if the attribute does not exist it is not relevant
            # this is because of scoping
            # FIXME: Make sure this is actually the case...
            continue
        if isinstance(attr_val, StructInstance):
            attr_val.valid = z3.If(cond, then_val.valid, attr_val.valid)
            merge_attrs(attr_val, cond, then_val.locals)
        elif isinstance(attr_val, z3.ExprRef):
            if then_val.sort() != attr_val.sort():
                attr_val = z3_cast(attr_val, then_val.sort())
            if_expr = z3.If(cond, then_val, attr_val)
            target_cls.set_or_add_var(then_name, if_expr)


def merge_list(cond, then_list, else_list):
    merged_list = []
    for idx, then_val in enumerate(then_list):
        else_val = else_list[idx]
        if isinstance(then_val, list):
            # note how we append, we do not extend
            # we want to maintain the nesting structure
            merged_list.append(merge_list(cond, then_val, else_val))
        else:
            merged_list.append(z3.If(cond, then_val, else_val))
    return merged_list


def mux_merge(cond, target, else_attrs):
    for idx, (member_name, _) in enumerate(target.fields):
        then_val = target.resolve_reference(member_name)
        else_val = else_attrs[idx]
        if isinstance(then_val, StructInstance):
            mux_merge(cond, then_val, else_val)
        else:
            if_expr = z3.If(cond, then_val, else_val)
            target.set_or_add_var(member_name, if_expr)


def handle_mux(cond, then_expr, else_expr):
    # TODO: Simplify this

    # we may return complex types, we have to unroll these
    if isinstance(then_expr, StructInstance):
        # record the validity
        then_valid = then_expr.valid
        # if the else expression is complex, we grab a list of the fields
        if isinstance(else_expr, StructInstance):
            else_valid = else_expr.valid
            fields = []
            for member_name, _ in else_expr.fields:
                fields.append(else_expr.resolve_reference(member_name))
            else_expr = fields
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
    if isinstance(else_expr, StructInstance):
        # record the validity
        else_valid = else_expr.valid
        # if the else expression is complex, we grab a list of the fields
        if isinstance(then_expr, StructInstance):
            then_valid = then_expr.valid
            fields = []
            for member_name, _ in then_expr.fields:
                fields.append(then_expr.resolve_reference(member_name))
            then_expr = fields
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
        merged_list = merge_list(cond, then_expr, else_expr)
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
    for member_name, _ in target.fields:
        member_val = target.resolve_reference(member_name)
        if isinstance(member_val, StructInstance):
            propagate_validity_bit(member_val, parent_valid)


@dataclass
class P4Parameter:
    __slots__ = ["mode", "name", "p4_type", "p4_default"]
    mode: str
    name: str
    p4_type: object
    p4_default: object


@dataclass
class P4Argument:
    __slots__ = ["mode", "p4_type", "p4_val"]
    mode: str
    p4_type: object
    p4_val: object


@dataclass
class Member:
    __slots__ = ["name", "p4_type", "width"]
    name: str
    p4_type: object
    width: int


class P4Z3Class():

    def eval(self, ctx):
        raise NotImplementedError("Method eval not implemented!")


class P4Expression(P4Z3Class):
    def eval(self, ctx):
        raise NotImplementedError("Method eval not implemented!")


class P4Statement(P4Z3Class):
    def eval(self, ctx):
        raise NotImplementedError("Method eval not implemented!")


class DefaultExpression(P4Z3Class):
    def __init__(self):
        pass

    def eval(self, ctx):
        pass


class OptionalExpression(P4Expression):
    def __init__(self, name, z3_type):
        self.name = name
        self.z3_type = z3_type

    def eval(self, ctx):
        return ctx.gen_instance(f"opt_{self.name}", self.z3_type)


class P4Range(P4Z3Class):
    def __init__(self, range_min, range_max):
        self.min = range_min
        self.max = range_max

    def eval(self, ctx):
        pass


class P4Mask(P4Z3Class):
    def __init__(self, value, mask):
        self.value = value
        self.mask = mask

    def eval(self, ctx):
        pass


class P4Declaration(P4Statement):
    # the difference between a P4Declaration and a ValueDeclaration is that
    # we resolve the variable in the ValueDeclaration
    # in the declaration we assign variables as is.
    # they are resolved at runtime by other classes
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def compute_rval(self, _ctx):
        return self.rval

    def eval(self, ctx):
        ctx.set_or_add_var(self.lval, self.compute_rval(ctx), True)


class ValueDeclaration(P4Declaration):
    def __init__(self, lval, rval, z3_type=None):
        super(ValueDeclaration, self).__init__(lval, rval)
        self.z3_type = z3_type

    def compute_rval(self, ctx):
        # this will only resolve expressions no other classes
        # FIXME: Untangle this a bit
        z3_type = ctx.resolve_type(self.z3_type)
        if self.rval is not None:
            rval = ctx.resolve_expr(self.rval)
            if isinstance(rval, int):
                if isinstance(z3_type, (z3.BitVecSortRef)):
                    rval = z3_cast(rval, z3_type)
            elif isinstance(rval, list):
                instance = ctx.gen_instance(UNDEF_LABEL, z3_type)
                instance.set_list(rval)
                rval = instance
            elif z3_type != rval.sort():
                msg = f"There was an problem setting {self.lval} to {rval}. " \
                    f"Type Mismatch! Target type {z3_type} " \
                    f"does not match with input type {rval.sort()}"
                raise RuntimeError(msg)
        else:
            rval = ctx.gen_instance(UNDEF_LABEL, z3_type)
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


class InstanceDeclaration(ValueDeclaration):
    def __init__(self, lval, p4z3_type, *args, **kwargs):
        super(InstanceDeclaration, self).__init__(lval, p4z3_type)
        self.args = args
        self.kwargs = kwargs

    def compute_rval(self, ctx):
        z3_type = ctx.resolve_type(self.rval)
        z3_type = z3_type.initialize(ctx, *self.args, **self.kwargs)
        return z3_type

    def eval(self, ctx):
        z3_type = self.compute_rval(ctx)
        ctx.set_or_add_var(self.lval, z3_type, True)


class P4Member():

    __slots__ = ["lval", "member", "evaluated"]

    def __init__(self, lval, member):
        self.lval = lval
        self.member = member

    def set_value(self, ctx, rval, reuse_index=False):
        if isinstance(self.lval, P4Index):
            self.lval.set_value(ctx, rval, self.member, reuse_index)
        else:
            target = ctx.resolve_reference(self.lval)
            target.set_or_add_var(self.member, rval)

    def __repr__(self):
        return f"{self.lval}.{self.member}"


class P4Index(P4Member):
    # FIXME: This class is an absolute nightmare. Completely broken
    __slots__ = ["lval", "member", "evaluated", "saved_member", "saved_lval"]

    def __init__(self, lval, member):
        self.lval = lval
        self.member = member
        self.evaluated = False
        self.saved_lval = lval
        self.saved_member = member

    def set_value(self, ctx, rval, target_member=None, reuse_index=False):
        if self.evaluated and reuse_index:
            index = self.saved_member
            lval = self.saved_lval
            log.info(index)
        else:
            index = ctx.resolve_expr(self.member)
            lval = ctx.resolve_expr(self.lval)
            self.saved_lval = index
            self.saved_member = lval
            self.evaluated = True

        if isinstance(index, z3.ExprRef):
            index = z3.simplify(index)

        if isinstance(index, z3.BitVecRef):
            max_idx = lval.resolve_reference("size")
            if target_member:
                for hdr_idx in range(max_idx):
                    hdr = lval.resolve_reference(str(hdr_idx))
                    cur_val = hdr.resolve_reference(target_member)
                    if_expr = handle_mux(index == hdr_idx, rval, cur_val)
                    hdr.set_or_add_var(target_member, if_expr)
            else:
                for hdr_idx in range(max_idx):
                    hdr = lval.resolve_reference(str(hdr_idx))
                    if_expr = handle_mux(index == hdr_idx, rval, hdr)
                    lval.set_or_add_var(hdr_idx, if_expr)
            return

        if isinstance(index, int):
            index = str(index)
        elif isinstance(index, z3.BitVecNumRef):
            index = str(index.as_long())
        else:
            raise RuntimeError(f"Unsupported index {type(index)}!")

        if target_member:
            hdr = lval.resolve_reference(str(index))
            hdr.set_or_add_var(target_member, rval)
        else:
            lval.set_or_add_var(index, rval)

    def __repr__(self):
        return f"{self.lval}[{self.member}]"


class P4Slice(P4Expression):
    def __init__(self, val, slice_l, slice_r):
        self.val = val
        self.slice_l = slice_l
        self.slice_r = slice_r

    def eval(self, ctx):
        val = ctx.resolve_expr(self.val)
        slice_l = ctx.resolve_expr(self.slice_l)
        slice_r = ctx.resolve_expr(self.slice_r)

        if isinstance(val, int):
            val = val.as_bitvec
        return z3.Extract(slice_l, slice_r, val)


class P4ComplexType():
    """ A P4ComplexType is a wrapper for any type that is not a simple Z3 type
    such as IntSort, BitVecSort or BoolSort.
    A P4ComplexType creates an P4ComplexInstance , all subtypes
    become fields of this class and be accessed in dot-notation
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
        self.fields = p4z3_type.fields
        self.valid = z3.BoolVal(True)

    def resolve_reference(self, var):
        if isinstance(var, P4Member):
            lval = self.locals[var.lval]
            var = lval.resolve_reference(var.member)
        elif isinstance(var, str):
            return self.locals[var]
        return var

    def set_list(self, rvals):
        for idx, (member_name, member_type) in enumerate(self.fields):
            val = rvals[idx]
            # integers need to be cast to the respective type
            if isinstance(val, int):
                val = z3_cast(val, member_type)
            self.set_or_add_var(member_name, val)
        # whenever we set a list, the target instances becomes valid
        self.valid = z3.BoolVal(True)

    def set_or_add_var(self, lval, rval, reuse_index=False):
        if isinstance(lval, P4Member):
            lval.set_value(self, rval, reuse_index=reuse_index)
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
        return f"{self.__class__.__name__}_{self.name}"

    def __eq__(self, other):
        # It can happen that we compare to a list
        # comparisons are almost the same just do not use fields
        if isinstance(other, P4ComplexInstance):
            other_list = []
            for other_member_name, _ in other.fields:
                other_list.append(other.resolve_reference(other_member_name))
        elif isinstance(other, list):
            other_list = other
        else:
            return z3.BoolVal(False)

        # there is a mismatch in fields, clearly not equal
        if len(self.fields) != len(other_list):
            return z3.BoolVal(False)

        eq_fields = []
        for index, (self_member_name, _) in enumerate(self.fields):
            self_member = self.resolve_reference(self_member_name)
            other_member = other_list[index]
            # we compare the fields of each complex type
            z3_eq = self_member == other_member
            eq_fields.append(z3_eq)
        return z3.And(*eq_fields)


class StructType(P4ComplexType):

    def __init__(self, name, ctx, fields, type_params):
        super(StructType, self).__init__(name)
        self.width = 0
        self.ctx = ctx
        self.fields = fields
        self.flat_names = []
        self.type_params = type_params
        self.initialize(ctx)

    def initialize(self, ctx):
        flat_names = []
        for idx, (member_name, member_type) in enumerate(self.fields):
            try:
                member_type = ctx.resolve_type(member_type)
            except KeyError:
                # A generic type, just use the string for now
                pass

            if isinstance(member_type, P4ComplexType):
                # the member is a complex type
                # retrieve it is flat list of fields
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
            self.fields[idx] = (member_name, member_type)

        if self.width == 0:
            # we are dealing with an empty struct, create a dummy datatype
            z3_type = z3.Datatype(self.name)
            z3_type.declare(f"mk_{self.name}")
            self.z3_type = z3_type.create()
        else:
            # use the flat bit width of the struct as datatype
            self.z3_type = z3.BitVecSort(self.width)
        self.flat_names = flat_names

    def instantiate(self, name, member_id=0):
        return StructInstance(name, self, member_id)

    def init_type_params(self, type_ctx, *args, **kwargs):
        init_struct = copy.copy(self)
        # bind the types and set the type ctx
        for idx, t_param in enumerate(init_struct.type_params):
            arg = type_ctx.resolve_type(args[idx])
            type_ctx.add_type(t_param, arg)
        init_struct.initialize(type_ctx)
        return init_struct

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result.type_params = copy.copy(self.type_params)
        result.fields = copy.copy(self.fields)
        result.flat_names = []
        return result

class StructInstance(P4ComplexInstance):

    def __init__(self, name, p4z3_type, member_id):
        super(StructInstance, self).__init__(name, p4z3_type, member_id)
        self.const = z3.Const(name, self.z3_type)

        # we use the overall index of the struct for a uniform naming scheme
        flat_idx = self.member_id
        for member_name, member_type in self.fields:

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
        # this bit_width must sum up to the bit width of the sub fields
        bit_width = self.width
        # set the fields of this class
        for sub_member in self.p4z3_type.flat_names:
            # TODO: Find a better way to handle undefined initialization
            # This is very coarse
            if str(bind_const) == UNDEF_LABEL:
                bind_var = z3.Const(UNDEF_LABEL, sub_member.p4_type)
            else:
                # we bind by extracting the respective bit range
                bind_var = z3.Extract(bit_width - 1,
                                      bit_width - sub_member.width, bind_const)
                if isinstance(sub_member.p4_type, z3.BoolSortRef):
                    # unfortunately bools still exit, we need to cast them
                    bind_var = z3_cast(bind_var, sub_member.p4_type)
            # set the new bind value
            self.set_or_add_var(sub_member.name, bind_var)
            bit_width -= sub_member.width

    def activate(self):
        # structs may contain headers that can be deactivated
        for member_name, _ in self.fields:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.activate()

    def deactivate(self):
        # structs may contain headers that can be deactivated
        for member_name, _ in self.fields:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.deactivate()

    def flatten(self, valid):
        if valid is None and isinstance(self, HeaderInstance):
            valid = self.valid
        fields = []
        for member_name, member_type in self.fields:
            member = self.resolve_reference(member_name)
            if isinstance(member, StructInstance):
                if isinstance(member, HeaderInstance):
                    sub_fields = member.flatten(member.valid)
                else:
                    sub_fields = member.flatten(valid)
                fields.extend(sub_fields)
            else:
                if valid is not None:
                    invalid_const = z3.Const("invalid", member_type)
                    member = z3.If(valid, member, invalid_const)
                    member = z3.simplify(member)
                fields.append(member)
        return fields


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

    def activate(self):
        for member_name, _ in self.fields:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.activate()
            # else:
                # # only if the header was invalid, reallocate all variables
                # if self.valid == z3.BoolVal(False):
                #     allocated_var = z3.Const(label, member_val.sort())
                #     self.set_or_add_var(member_name, allocated_var)
        self.valid = z3.BoolVal(True)

    def deactivate(self):
        for member_name, member_type in self.fields:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.deactivate()
            else:
                member_const = z3.Const(UNDEF_LABEL, member_type)
                self.set_or_add_var(member_name, member_const)
        self.valid = z3.BoolVal(False)

    def isValid(self, _ctx=None):
        # This is a built-in
        return self.valid

    def setValid(self, ctx):
        if self.union_parent:
            # this is a hacky way to invalidate other fields
            # in the case that this header is part of a union
            union = self.union_parent
            for member_name, _ in union.fields:
                member_hdr = union.resolve_reference(member_name)
                # check whether the header is the same object
                # any other header is now invalid
                if member_hdr is not self:
                    member_hdr.setInvalid(ctx)
        # This is a built-in
        self.activate()

    def setInvalid(self, _ctx):
        if self.union_parent:
            # this is a hacky way to invalidate other fields
            # in the case that this header is part of a union
            union = self.union_parent
            for member_name, _ in union.fields:
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

            self_const = self.flatten(z3.BoolVal(True))
            other_const = other.flatten(z3.BoolVal(True))
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


class UnionType(StructType):
    def instantiate(self, name, member_id=0):
        return UnionInstance(name, self, member_id)

class UnionInstance(StructInstance):

    def __init__(self, name, p4z3_type, member_id):
        # TODO: Check if this class is implemented correctly...
        super(UnionInstance, self).__init__(name, p4z3_type, member_id)


class HeaderUnionType(StructType):
    def instantiate(self, name, member_id=0):
        return HeaderUnionInstance(name, self, member_id)


class HeaderUnionInstance(StructInstance):

    def __init__(self, name, p4z3_type, member_id):
        # TODO: Check if this class is implemented correctly...
        super(HeaderUnionInstance, self).__init__(name, p4z3_type, member_id)
        for member_name, _ in self.fields:
            member_hdr = self.resolve_reference(member_name)
            member_hdr.bind_to_union(self)
        self.locals["isValid"] = self.isValid

    @ property
    def valid(self):
        valid_list = []
        for member_name, _ in self.fields:
            member_hdr = self.resolve_reference(member_name)
            valid_list.append(member_hdr.isValid())
        return z3.simplify(z3.Or(*valid_list))

    def isValid(self, _ctx=None):
        # This is a built-in
        return self.valid

    def __setattr__(self, name, val):
        # FIXME: Fix this workaround for valid attributes
        if name == "valid":
            # do not override the custom valid computation here
            # header union validity is dependent on its fields
            pass
        else:
            self.__dict__[name] = val

    def __copy__(self):
        result = super(HeaderUnionInstance, self).__copy__()
        # we need to update the reference of the function to the new object
        # quite nasty...
        result.locals["isValid"] = result.isValid
        for member_name, _ in result.fields:
            member_hdr = result.resolve_reference(member_name)
            member_hdr.bind_to_union(result)
        return result


class ListType(StructType):

    def __init__(self, name, ctx, fields):
        for idx, arg in enumerate(fields):
            fields[idx] = (f"f{idx}", arg)
            # some little hack to automatically infer a random type name
            name += str(arg)
        super(ListType, self).__init__(name, ctx, fields, [])

    def instantiate(self, name, member_id=0):
        return ListInstance(name, self, member_id)


class ListInstance(StructInstance):
    pass


class ParserException(Exception):
    pass


class HeaderStack(StructType):

    def __init__(self, name, ctx, fields):
        for idx, arg in enumerate(fields):
            fields[idx] = (f"{idx}", arg)
        super(HeaderStack, self).__init__(name, ctx, fields, [])

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
            # This is a built-in defined in the spec
            try:
                next_id = z3.simplify(self.parent_hdr.locals["nextIndex"])
                hdr = self.parent_hdr.locals[str(next_id)]
            except KeyError:
                raise ParserException("Index out of bounds!")
            return hdr

        if key == "last":
            # This is a built-in defined in the spec
            try:
                last_idx = z3.simplify(self.parent_hdr.locals["lastIndex"])
                hdr = self.parent_hdr.locals[str(last_idx)]
            except KeyError:
                raise ParserException("Index out of bounds!")
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
        self.locals["nextIndex"] = z3.BitVecVal(0, 32)
        self.locals["push_front"] = self.push_front
        self.locals["pop_front"] = self.pop_front
        self.locals["size"] = len(self.fields)
        # FIXME: This should be undefined...
        self.locals["lastIndex"] = self.locals["nextIndex"]

    def push_front(self, ctx, count):
        # This is a built-in defined in the spec
        for hdr_idx in range(0, self.locals["size"]):
            if hdr_idx < count:
                hdr = self.locals[f"{hdr_idx}"]
                hdr.setInvalid(ctx)
        self.locals["nextIndex"] += count
        if z3.is_true(z3.simplify(self.locals["nextIndex"] > self.locals["size"])):
            self.locals["nextIndex"] = z3.BitVecVal(self.locals["size"], 32)
        self.locals["lastIndex"] = self.locals["nextIndex"]

    def pop_front(self, ctx, count):
        # This is a built-in defined in the spec
        last_range = self.locals["size"] - count
        last_range = 0 if last_range < 0 else last_range
        for hdr_idx in range(last_range, self.locals["size"]):
            if hdr_idx < self.locals["size"] - 1:
                hdr = self.locals[f"{hdr_idx}"]
                hdr.setInvalid(ctx)

        self.locals["nextIndex"] -= count
        self.locals["lastIndex"] = self.locals["nextIndex"]
        if z3.is_true(z3.simplify(self.locals["nextIndex"] < 0)):
            self.locals["nextIndex"] = z3.BitVecVal(0, 32)
            self.locals["lastIndex"] = z3.BitVecVal(0, 32)

    def __copy__(self):
        result = super(HeaderStackInstance, self).__copy__()
        # update references to the method calls
        result.locals["push_front"] = result.push_front
        result.locals["pop_front"] = result.pop_front
        result.locals = HeaderStackDict(result.locals, result)
        return result


class StaticType():
    locals = {}

    def resolve_reference(self, var):
        if isinstance(var, P4Member):
            lval = self.locals[var.lval]
            var = lval.resolve_reference(var.member)
        elif isinstance(var, str):
            var = self.locals[var]
        return var

class Enum(StaticType):

    def __init__(self, name, fields):
        self.locals = {}
        self.name = name
        self.z3_type = z3.BitVecSort(32)
        for idx, enum_name in enumerate(fields):
            self.locals[enum_name] = z3.BitVecVal(idx, 32)
        self.fields = fields

    def instantiate(self, _name, _member_id=0):
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

    def __init__(self, name, fields, z3_type):
        self.name = name
        self.z3_type = z3_type
        self.locals = {}
        self.fields = fields
        for field_name, field_val in fields:
            self.locals[field_name] = field_val


class P4Extern(StaticType):
    # Externs are P4ComplexInstance in name only...
    def __init__(self, name, type_params, methods):
        self.name = name
        z3_type = z3.Datatype(name)
        z3_type.declare(f"mk_{name}")
        self.z3_type = z3_type.create()
        self.type_params = type_params
        self.type_ctx = {}
        # attach the methods
        self.locals = {}
        for method in methods:
            self.locals.setdefault(method.lval, []).append(method.rval)

    def init_type_params(self, ctx, *args, **kwargs):
        init_extern = copy.copy(self)
        # bind the types and set the type ctx
        for idx, t_param in enumerate(init_extern.type_params):
            arg = ctx.resolve_type(args[idx])
            init_extern.type_ctx[t_param] = arg
        # the types bound in an extern also apply to its objects
        for method_list in init_extern.locals.values():
            for method in method_list:
                method.extern_ctx = init_extern.type_ctx
        return init_extern

    def initialize(self, _ctx, *args, **kwargs):
        # FIXME: Try to understand constructor args and what they mean
        # Example: psa-hash.p4
        return self

    def __repr__(self):
        return self.name

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

    def init_type_params(self, ctx, *args, **kwargs):
        init_ctrl_type = copy.copy(self)
        # bind the types and set the type ctx
        for idx, t_param in enumerate(init_ctrl_type.type_params):
            init_ctrl_type.type_ctx[t_param] = args[idx]
        return init_ctrl_type


class P4ParserType(P4ControlType):
    pass
