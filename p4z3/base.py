from collections import deque, OrderedDict
from dataclasses import dataclass
import types
import copy
import logging
import z3
from z3int import Z3Int

log = logging.getLogger(__name__)


def gen_instance(var_name, p4z3_type):
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


def copy_attrs(attrs):
    attr_copy = {}
    for attr_name, attr_val in attrs.items():
        if isinstance(attr_val, P4ComplexInstance):
            attr_val = copy.copy(attr_val)
        attr_copy[attr_name] = attr_val
    return attr_copy


def merge_attrs(cond, then_attrs, target_attrs):
    for then_name, then_val in then_attrs.items():
        try:
            attr_val = target_attrs[then_name]
        except KeyError:
            # if the attribute does not exist it is not relevant
            # this is because of scoping
            # FIXME: Make sure this is actually the case...
            continue
        if isinstance(attr_val, P4ComplexInstance):
            attr_val.valid = z3.simplify(
                z3.If(cond, then_val.valid, attr_val.valid))
            merge_attrs(cond, then_val.locals, attr_val.locals)
        elif isinstance(attr_val, z3.ExprRef):
            if then_val.sort() != attr_val.sort():
                attr_val = z3_cast(attr_val, then_val.sort())
            if_expr = z3.simplify(z3.If(cond, then_val, attr_val))
            target_attrs[then_name] = if_expr


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


class P4Declaration(P4Statement):
    # the difference between a P4Declaration and a ValueDeclaration is that
    # we resolve the variable in the ValueDeclaration
    # in the declaration we assign variables as is.
    # they are resolved at runtime by other classes
    def __init__(self, lval, rval):
        self.name = lval
        self.rval = rval

    def eval(self, p4_state):
        p4_state.set_or_add_var(self.name, self.rval)


class ValueDeclaration(P4Statement):
    def __init__(self, lval, rval, z3_type):
        self.lval = lval
        self.rval = rval
        self.z3_type = z3_type

    def eval(self, p4_state):
        # this will only resolve expressions no other classes
        # FIXME: Untangle this a bit
        if self.rval is not None:
            rval = p4_state.resolve_expr(self.rval)
            if isinstance(rval, int):
                if isinstance(self.z3_type, (z3.BitVecSortRef)):
                    rval = z3_cast(rval, self.z3_type)
            elif isinstance(rval, list):
                instance = gen_instance("undefined", self.z3_type)
                instance.set_list(rval)
                rval = instance
            elif self.z3_type != rval.sort():
                msg = f"There was an problem setting {self.lval} to {rval}. " \
                    f"Type Mismatch! Target type {self.z3_type} " \
                    f"does not match with input type {rval.sort()}"
                raise RuntimeError(msg)
        else:
            rval = gen_instance("undefined", self.z3_type)
        p4_state.set_or_add_var(self.lval, rval)

class P4Member(P4Expression):

    def __init__(self, lval, member):
        self.lval = lval
        self.member = member

    def eval(self, p4_state):
        lval = self.lval
        member = self.member
        while isinstance(lval, P4Member):
            lval = lval.eval(p4_state)
        while isinstance(member, P4Member):
            member = member.eval(p4_state)
        if isinstance(lval, (P4Z3Class, P4ComplexInstance)):
            lval = p4_state.resolve_expr(lval)
            return lval.locals[member]
        return f"{lval}.{member}"


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

    def __init__(self, name, z3_args):
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
        log.debug("Resolving reference %s", var)
        if isinstance(var, str):
            sub_class = self
            if '.' in var:
                # this means we are accessing a complex member
                # get the parent class and update its value
                prefix, suffix = var.rsplit(".", 1)
                # prefix may be a pointer to an actual complex type, resolve it
                sub_class = self.resolve_reference(prefix)
                var = sub_class.locals[suffix]
            else:
                var = self.locals[var]
        return var

    def set_list(self, rvals):
        self.valid = z3.BoolVal(True)
        for idx, (member_name, member_type) in enumerate(self.members):
            val = rvals[idx]
            # integers need to be cast to the respective type
            if isinstance(val, int):
                val = z3_cast(val, member_type)
            self.set_or_add_var(member_name, val)

    def _update_dict(self, lval, rval, target_dict):
        # now that all the preprocessing is done we can assign the value
        log.debug("Setting %s(%s) to %s(%s) ",
                  lval, type(lval), rval, type(rval))
        if '.' in lval:
            # this means we are accessing a complex member
            # get the parent class and update its value
            prefix, suffix = lval.rsplit(".", 1)
            log.debug("Recursing with %s and %s ", prefix, suffix)
            # prefix may be a pointer to an actual complex type, resolve it
            target_class = self.resolve_reference(prefix)
            target_class.set_or_add_var(suffix, rval)
        else:
            if lval in target_dict:
                # the target variable exists
                # do not override an existing variable with a string reference!
                # resolve any possible rvalue reference
                rval = self.resolve_reference(rval)
                # rvals could be a list, unroll the assignment
                if isinstance(rval, list):
                    tmp_lval = self.resolve_reference(lval)
                    if isinstance(tmp_lval, P4ComplexInstance):
                        tmp_lval.set_list(rval)
                    else:
                        raise TypeError(
                            f"set_list {type(tmp_lval)} not supported!")
                    return
            target_dict[lval] = rval

    def set_or_add_var(self, lval, rval):
        self._update_dict(lval, rval, self.locals)

    def sort(self):
        return self.p4z3_type

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

    def activate(self, label="undefined"):
        pass

    def deactivate(self, label="undefined"):
        pass

    def propagate_validity_bit(self, parent_valid=None):
        if parent_valid is not None:
            self.valid = parent_valid
        # structs can be contained in headers so they can also be deactivated...
        for member_name, _ in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.propagate_validity_bit(parent_valid)

    def check_validity(self, parent_validity=None):
        for member_name, member_type in self.members:
            # retrieve the member we are accessing
            member = self.resolve_reference(member_name)
            if isinstance(member, P4ComplexInstance):
                # it is a complex type
                # propagate the validity to all children
                member.check_validity(parent_validity)
            else:
                if parent_validity is None:
                    continue
                # if the header is invalid set the variable to "undefined"
                cond = z3.simplify(z3.If(parent_validity, member,
                                         z3.Const("invalid", member_type)))
                self.set_or_add_var(member_name, cond)


class StructType(P4ComplexType):

    def __init__(self, name, z3_args):
        super(StructType, self).__init__(name, z3_args)

        flat_names = []
        self.width = 0
        for member_name, member_type in z3_args:
            if isinstance(member_type, P4ComplexType):
                # the member is a complex type
                # retrieve it is flat list of members
                # append it to the member list
                for sub_member in member_type.flat_names:
                    member = Member(f"{member_name}.{sub_member.name}",
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

        if self.width == 0:
            # we are dealing with an empty struct, create a dummy datatype
            z3_type = z3.Datatype(name)
            z3_type.declare(f"mk_{name}")
            self.z3_type = z3_type.create()
        else:
            # use the flat bit width of the struct as datatype
            self.z3_type = z3.BitVecSort(self.width)
        self.z3_args = z3_args
        self.flat_names = flat_names

    def instantiate(self, name, member_id=0):
        return StructInstance(name, self, member_id)


class StructInstance(P4ComplexInstance):

    def __init__(self, name, p4z3_type, member_id):
        super(StructInstance, self).__init__(name, p4z3_type, member_id)
        self.const = z3.Const(name, p4z3_type.z3_type)

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
        bit_width = self.p4z3_type.width
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
            if isinstance(member_val, P4ComplexInstance):
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
            if isinstance(member_val, P4ComplexInstance):
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
        self.union_parent = union_instance

    def propagate_validity_bit(self, parent_valid=None):
        if parent_valid is None:
            self.valid = z3.Bool(f"{self.name}_valid")
        parent_valid = self.valid
        # structs can be contained in headers so they can also be deactivated...
        for member_name, _ in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.propagate_validity_bit(parent_valid)

    def check_validity(self, parent_validity=None):
        if parent_validity is None:
            parent_validity = self.valid
        for member_name, member_type in self.members:
            # retrieve the member we are accessing
            member = self.resolve_reference(member_name)
            if isinstance(member, P4ComplexInstance):
                # it is a complex type
                # propagate the validity to all children
                member.check_validity(parent_validity)
            else:
                if parent_validity is None:
                    continue

                # if the header is invalid set the variable to "undefined"
                cond = z3.simplify(z3.If(parent_validity, member,
                                         z3.Const("invalid", member_type)))
                self.set_or_add_var(member_name, cond)

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
            return z3.Or(check_invalid, comparison)
        return super().__eq__(other)

    def __copy__(self):
        result = super(HeaderInstance, self).__copy__()
        # we need to update the reference of the function to the new object
        # quite nasty...
        result.locals["isValid"] = result.isValid
        result.locals["setValid"] = result.setValid
        result.locals["setInvalid"] = result.setInvalid
        return result


class HeaderUnionType(HeaderType):
    def instantiate(self, name, member_id=0):
        return HeaderUnionInstance(name, self, member_id)


class HeaderUnionInstance(HeaderInstance):

    def __init__(self, name, p4z3_type, member_id):
        # TODO: Check if this class is implemented correctly...
        super(HeaderUnionInstance, self).__init__(name, p4z3_type, member_id)
        for member_name, _ in self.members:
            member_hdr = self.resolve_reference(member_name)
            member_hdr.bind_to_union(self)

    def isValid(self, p4_state=None):
        valid_list = []
        for member_name, _ in self.members:
            member_hdr = self.resolve_reference(member_name)
            valid_list.append(member_hdr.isValid())
        return z3.Or(*valid_list)


class ListType(StructType):

    def __init__(self, name, z3_args):
        for idx, arg in enumerate(z3_args):
            z3_args[idx] = (f"{idx}", arg)
            # some little hack to automatically infer a random type name
            name += str(arg)
        super(ListType, self).__init__(name, z3_args)

    # TODO: Implement this class correctly...
    def instantiate(self, name, member_id=0):
        return ListInstance(name, self, member_id)


class ListInstance(StructInstance):
    pass


class HeaderStack(StructType):

    def __init__(self, name, z3_args):
        for idx, arg in enumerate(z3_args):
            z3_args[idx] = (f"{idx}", arg)
        super(HeaderStack, self).__init__(name, z3_args)

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
        self.locals["lastIndex"] = z3.BitVecVal(self.nextIndex, 32) - 1

    def push_front(self, p4_state, num):
        # This is a built-in
        # TODO: Check if this implementation makes sense
        for hdr_idx in range(1, num):
            hdr_idx = hdr_idx - 1
            try:
                hdr = self.resolve_reference(f"{hdr_idx}")
                hdr.setValid(p4_state)
            except KeyError:
                pass

    def pop_front(self, p4_state, num):
        # This is a built-in
        # TODO: Check if this implementation makes sense
        for hdr_idx in range(1, num):
            hdr_idx = hdr_idx - 1
            try:
                hdr = self.resolve_reference(f"{hdr_idx}")
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
        # FIXME: Unify types
        z3_type = z3.Datatype(name)
        z3_type.declare(f"mk_{name}")
        self.members = []
        self.z3_type = z3_type.create()
        self.const = z3.Const(name, self.z3_type)
        self.locals = {}
        # simple fix for now until I know how to initialize params for externs
        self.params = {}
        self.name = name
        self.type_params = type_params
        # these are method declarations, not methods
        for method in methods:
            self.locals[method.name] = method.rval
        # dummy
        self.valid = False

    def init_type_params(self, *args, **kwargs):
        # the extern is instantiated, we need to copy it
        init_extern = self.initialize()
        for idx, t_param in enumerate(init_extern.type_params):
            for method in init_extern.locals.values():
                # bind the method return type
                if method.return_type == t_param:
                    method.return_type = args[idx]
                # bind the method parameters
                for method_param in method.params:
                    if method_param.p4_type == t_param:
                        method_param.p4_type = args[idx]
        return init_extern

    def initialize(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        instance = copy.copy(self)
        return instance

    def __call__(self, *args, **kwargs):
        return self.initialize(*args, **kwargs)

    def __repr__(self):
        return self.name

    def deactivate(self):
        log.warning("This method should not be called...")


class P4ControlType(P4Extern):
    pass


class P4ParserType(P4Extern):
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

    def add_to_buffer(self, var_dict):
        self.var_buffer = {**self.var_buffer, **var_dict}

    def prepend_to_buffer(self, var_dict):
        self.var_buffer = {**var_dict, **self.var_buffer}

    def copy_out(self, p4_state):
        # FIXME: This does not respect local context
        # local variables are overridden in functions and controls
        # restore any variables that may have been overridden
        for param_name, param in self.var_buffer.items():
            is_ref = param[0]
            param_ref = param[1]
            param_val = param[2]
            if is_ref in ("inout", "out"):
                val = p4_state.resolve_reference(param_name)
            if param_val is None:
                # value has not existed previously, marked for deletion
                log.debug("Deleting %s", param_name)
                p4_state.del_var(param_name)
            else:
                log.debug("Resetting %s to %s", param_name, type(param_val))
                p4_state.set_or_add_var(param_name, param_val)

            if is_ref in ("inout", "out"):
                # with copy-out we copy from left to right
                # values on the right override values on the left
                # the var buffer is an ordered dict that maintains this order
                log.debug("Copy-out: %s to %s", val, param_val)
                p4_state.set_or_add_var(param_ref, val)

    def eval(self, p4_state):
        self.copy_out(p4_state)


class P4State():
    """
    A P4State Object is a special, dynamic type of P4ComplexType. It represents
    the execution environment and its z3 representation is ultimately used to
    compare different programs. P4State is mostly just a wrapper for all inout
    values. It also manages the execution chain of the program.
    """

    def __init__(self, name, z3_args, global_values, instances):
        self.name = name
        # deques allow for much more efficient pop and append operations
        # this is all we do so this works well
        self.globals = global_values
        self.locals = {}
        self.has_exited = False
        self.exit_states = deque()
        self.contexts = deque()
        self.valid = z3.BoolVal(False)
        self.members = z3_args

        for instance_name, instance_val in instances.items():
            self.locals[instance_name] = instance_val

        flat_args = []
        self.flat_names = []
        idx = 0
        for z3_arg_name, z3_arg_type in z3_args:
            if isinstance(z3_arg_type, P4ComplexType):
                member_cls = z3_arg_type.instantiate(f"{name}.{idx}")
                for sub_member in z3_arg_type.flat_names:
                    flat_args.append((f"{idx}", sub_member.p4_type))
                    self.flat_names.append(f"{z3_arg_name}.{sub_member.name}")
                    idx += 1
                # this is a complex datatype, create a P4ComplexType
                self.locals[z3_arg_name] = member_cls
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
            self.set_or_add_var(arg_name, member_constructor(self.const))

    def del_var(self, var_string):
        # simple wrapper for delattr
        self.locals.pop(var_string, None)

    def resolve_expr(self, expr):
        # Resolves to z3 and z3p4 expressions, ints, lists, and dicts are also okay
        # resolve potential string references first
        log.debug("Resolving %s", expr)
        if isinstance(expr, str):
            val = self.resolve_reference(expr)
        else:
            val = expr
        if isinstance(val, P4Expression):
            # We got a P4 expression, recurse and resolve...
            val = val.eval(self)
            return self.resolve_expr(val)
        if isinstance(val, (z3.AstRef, int)):
            # These are z3 types and can be returned
            # Unfortunately int is part of it because z3 is very inconsistent
            # about var handling...
            return val
        if isinstance(val, (P4ComplexInstance, P4Z3Class, types.MethodType)):
            # If we get a whole class return a new reference to the object
            # Do not return the z3 type because we may assign a complete structure
            # In a similar manner, just return any remaining class types
            # Methods can be class attributes and also need to be returned as is
            return val
        if isinstance(val, list):
            # For lists, resolve each value individually and return a new list
            list_expr = []
            for val_expr in val:
                rval_expr = self.resolve_expr(val_expr)
                list_expr.append(rval_expr)
            return list_expr
        raise TypeError(f"Value of type {type(val)} cannot be resolved!")

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

    def set_or_add_var(self, lval, rval):
        if isinstance(lval, P4Member):
            lval = lval.eval(self)
        if isinstance(lval, P4Slice):
            self.set_slice(lval, rval)
            return
        # now that all the preprocessing is done we can assign the value
        log.debug("Setting %s(%s) to %s(%s) ",
                  lval, type(lval), rval, type(rval))
        if '.' in lval:
            # this means we are accessing a complex member
            # get the parent class and update its value
            prefix, suffix = lval.rsplit(".", 1)
            log.debug("Recursing with %s and %s ", prefix, suffix)
            # prefix may be a pointer to an actual complex type, resolve it
            target_class = self.resolve_reference(prefix)
            target_class.set_or_add_var(suffix, rval)
        else:
            if lval in self.locals:
                # the target variable exists
                # do not override an existing variable with a string reference!
                # resolve any possible rvalue reference
                rval = self.resolve_reference(rval)
                # rvals could be a list, unroll the assignment
                if isinstance(rval, list):
                    tmp_lval = self.resolve_reference(lval)
                    if isinstance(tmp_lval, P4ComplexInstance):
                        tmp_lval.set_list(rval)
                    else:
                        raise TypeError(
                            f"set_list {type(tmp_lval)} not supported!")
                    return
            self.locals[lval] = rval

    def get_z3_repr(self) -> z3.DatatypeRef:
        ''' This method returns the current representation of the object in z3
        logic.'''
        members = []
        for member_name, _ in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                # first we need to make sure that validity is correct
                member_val.check_validity()
                members.extend(member_val.flatten())
            else:
                members.append(member_val)
        return self.z3_type.constructor(0)(*members)

    def resolve_reference(self, var):
        if isinstance(var, P4Member):
            var = var.eval(self)
        log.debug("Resolving reference %s", var)
        if isinstance(var, str):
            if '.' in var:
                # this means we are accessing a complex member
                # get the parent class and update its value
                prefix, suffix = var.rsplit(".", 1)
                # prefix may be a pointer to an actual complex type, resolve it
                if prefix:
                    sub_class = self.resolve_reference(prefix)
                else:
                    sub_class = self
                var = sub_class.locals[suffix]
            else:
                try:
                    var = self.locals[var]
                except KeyError:
                    var = self.globals[var]
        return var

    def checkpoint(self):
        var_store = {}
        for attr_name, attr_val in self.locals.items():
            if isinstance(attr_val, z3.AstRef):
                var_store[attr_name] = attr_val
            elif isinstance(attr_val, P4ComplexInstance):
                var_store[attr_name] = copy.copy(attr_val)
            # this is only required because of some issues with duplicate
            # states in the parser FIXME
            elif isinstance(attr_val, P4Expression):
                var_store[attr_name] = copy.copy(attr_val)
        contexts = self.contexts.copy()
        return var_store, contexts

    def restore(self, var_store, contexts=None):
        for attr_name, attr_val in var_store.items():
            self.locals[attr_name] = attr_val
        if contexts:
            self.contexts = contexts


class Z3Reg():
    def __init__(self):
        self._types = {}
        self.p4_state = P4State("global_state", {}, {}, {})

    def declare_global(self, p4_class=None):
        if not p4_class:
            # TODO: Get rid of unimplemented expressions
            return
        if isinstance(p4_class, P4ComplexType):
            name = p4_class.name
            self._types[name] = p4_class
        elif isinstance(p4_class, P4Extern):
            name = p4_class.name
            self._types[name] = p4_class
            # I hate externs so much...
            self.p4_state.globals[name] = p4_class.initialize()
        elif isinstance(p4_class, (Enum)):
            # enums are special static types
            # we need to add them to the list of accessible variables
            # and their type is actually the z3 type, not the class type
            name = p4_class.name
            self.p4_state.globals[name] = p4_class
            self._types[name] = p4_class.z3_type
        elif isinstance(p4_class, P4Declaration):
            # FIXME: Typedefs should not be added here
            name = p4_class.name
            self.p4_state.globals[name] = p4_class.rval
            self._types[name] = p4_class.rval
        elif isinstance(p4_class, ValueDeclaration):
            # FIXME: Typedefs should not be added here
            p4_class.eval(self.p4_state)
            name = p4_class.lval
            rval = self.p4_state.resolve_reference(name)
            self.p4_state.globals[name] = rval
            self._types[name] = rval
        else:
            raise RuntimeError(
                "Unsupported global declaration %s" % type(p4_class))

    def init_p4_state(self, name, p4_params):
        stripped_args = []
        instances = {}
        for param in p4_params:
            if param.is_ref in ("inout", "out"):
                # only inouts or outs matter as output
                stripped_args.append((param.name, param.p4_type))
            else:
                # for inputs we can instantiate something
                instance = gen_instance(param.name, param.p4_type)
                instances[param.name] = instance
        p4_state = P4State(name, stripped_args,
                           self.p4_state.globals, instances)
        for member_name, member_type in p4_state.members:
            member_val = p4_state.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.propagate_validity_bit()
        return p4_state

    def type(self, type_name):
        if type_name in self._types:
            z3_type = self._types[type_name]
            return self._types[type_name]
        else:
            # lets be bold here and assume that if a  type is not known
            # it is a user-defined or generic can be declared generically
            z3_type = z3.DeclareSort(type_name)
            self._types[type_name] = z3_type
            return z3_type

    def stack(self, z3_type, num):
        # Header stacks are a bit special because they are basically arrays
        # with specific features
        # We need to declare a new z3 type and add a new complex class
        name = f"{z3_type}{num}"
        p4_stack = HeaderStack(name, [z3_type] * num)
        self.declare_global(p4_stack)
        return self.type(name)

    def get_value(self, expr):
        val = None
        if isinstance(expr, P4Expression):
            val = expr.get_value()
        elif isinstance(expr, str):
            val = self.p4_state.globals[expr]
        else:
            raise RuntimeError(
                "Unsupported value expression %s" % type(expr))
        if isinstance(val, z3.BitVecNumRef):
            # unfortunately, we need to get the real int value here
            val = Z3Int(val.as_long(), val.size())
        return val
