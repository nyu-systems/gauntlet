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
        type_name = p4z3_type.name
        if var_name is None:
            var_name = f"{type_name}"
        p4z3_type.ref_count += 1
        z3_cls = p4z3_type.instantiate(var_name)
        z3_cls.deactivate()
        return z3_cls
    elif isinstance(p4z3_type, P4ComplexInstance):
        # static complex type, just return
        return p4z3_type
    elif isinstance(p4z3_type, z3.SortRef):
        return z3.Const(f"{var_name}", p4z3_type)
    elif isinstance(p4z3_type, list):
        instantiated_list = []
        for idx, z3_type in enumerate(p4z3_type):
            const = z3.Const(f"{var_name}{idx}", z3_type)
            instantiated_list.append(const)
        return instantiated_list
    raise RuntimeError(f"{p4z3_type} instantiation not supported!")


def merge_parameters(params, *args, **kwargs):
    # FIXME: This function could be a lot more efficient...
    # FIXME: Overloading does not work correctly here
    merged_args = {}
    args_len = len(args)
    for idx, param in enumerate(params):
        if idx < args_len:
            arg_val = args[idx]
            if isinstance(arg_val, DefaultExpression):
                # Default expressions are pointless arguments, so skip them
                continue
            arg = P4Argument(param.is_ref, param.p4_type, arg_val)
            merged_args[param.name] = arg
        elif param.p4_default is not None:
            # there is no argument but we have a default value, so use that
            arg_val = param.p4_default
            arg = P4Argument(param.is_ref, param.p4_type, arg_val)
            merged_args[param.name] = arg
    for param_name, arg_val in kwargs.items():
        # this is expensive but at least works reliably
        if isinstance(arg_val, DefaultExpression):
            # Default expressions are pointless arguments, so skip them
            continue
        for param in params:
            if param.name == param_name:
                arg = P4Argument(param.is_ref, param.p4_type, arg_val)
                merged_args[param_name] = arg
    return merged_args


def save_variables(p4_state, merged_args):
    var_buffer = OrderedDict()
    # save all the variables that may be overridden
    for param_name, arg in merged_args.items():
        is_ref = arg.is_ref
        param_ref = arg.p4_val
        # if the variable does not exist, set the value to None
        try:
            param_val = p4_state.resolve_reference(param_name)
            if not isinstance(param_val, z3.AstRef):
                param_val = copy.copy(param_val)
            var_buffer[param_name] = (is_ref, param_ref, param_val)
        except KeyError:
            var_buffer[param_name] = (is_ref, param_ref, None)
    return var_buffer


def copy_attrs(attrs):
    attr_copy = {}
    for attr_name, attr_val in attrs.items():
        if isinstance(attr_val, P4ComplexInstance):
            attr_val = copy.copy(attr_val)
        attr_copy[attr_name] = attr_val
    return attr_copy


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


class P4Declaration(P4Statement):
    # the difference between a P4Declaration and a P4Assignment is that
    # we resolve the variable in the P4Assignment
    # in the declaration we assign variables as is.
    # they are resolved at runtime by other classes
    def __init__(self, lval, rval, z3_type=None):
        self.lval = lval
        self.rval = rval
        self.z3_type = z3_type

    def eval(self, p4_state):
        # this will only resolve expressions no other classes
        # FIXME: Untagle this a bit
        if self.rval is not None:
            rval = p4_state.resolve_expr(self.rval)
            if self.z3_type is not None:
                if isinstance(rval, int):
                    if isinstance(self.z3_type, (z3.BitVecSortRef)):
                        rval = z3_cast(rval, self.z3_type)
                elif self.z3_type != rval.sort():
                    msg = f"There was an problem setting {self.lval} to {rval}. " \
                        f"Type Mismatch! Target type {self.z3_type} " \
                        f"does not match with input type {rval.sort()}"
                    raise RuntimeError(msg)
        else:
            rval = gen_instance("undefined", self.z3_type)
        p4_state.set_or_add_var(self.lval, rval)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)

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
        if isinstance(lval, P4Z3Class):
            lval = p4_state.resolve_expr(lval)
            return lval.p4_attrs[member]
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
    A P4ComplexType creates an instance of a Z3 DataTypeRef, all subtypes
    become members of this class and be accessed in dot-notation
    (e.g., headers.eth.srcmac).
    If one of the children is a DataTypeRef a new P4ComplexType will be
    instantiated and attached as member.
    Every member of this class should either be a P4ComplexType or a z3.SortRef
     if it is a basic type. A DataTypeRef should never be a member and always
    needs to be converted to a P4ComplexType.
    """

    def __init__(self, name, z3_args):
        self.name = name
        self.ref_count = 0
        z3_type = z3.Datatype(name)
        stripped_args = []
        for z3_arg in z3_args:
            z3_arg_name = z3_arg[0]
            z3_arg_type = z3_arg[1]
            if isinstance(z3_arg_type, P4ComplexType):
                stripped_args.append((z3_arg_name, z3_arg_type.z3_type))
            else:
                stripped_args.append(z3_arg)
        z3_type.declare(f"mk_{name}", *stripped_args)
        self.z3_type = z3_type.create()
        self.z3_args = z3_args

    def instantiate(self, name, parent_const=None):
        return P4ComplexInstance(name, self, parent_const)

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
    def __init__(self, name, p4z3_type, parent_const=None):
        self.p4_attrs = {}
        self.name = name
        self.z3_type = p4z3_type.z3_type
        self.p4z3_type = p4z3_type
        self.const = z3.Const(f"{name}", self.z3_type)
        if parent_const is not None:
            bind_const = parent_const
        else:
            bind_const = self.const
        self.members = OrderedDict()
        # set the members of this class
        for type_index, z3_arg in enumerate(p4z3_type.z3_args):
            z3_arg_name = z3_arg[0]
            z3_arg_type = z3_arg[1]
            var_name = f"{name}.{z3_arg_name}"
            member_constructor = self.z3_type.accessor(0, type_index)
            z3_member = member_constructor(bind_const)
            if isinstance(z3_arg_type, P4ComplexType):
                # this is a complex datatype, create a P4ComplexType
                member_cls = z3_arg_type.instantiate(var_name, z3_member)
                self.p4_attrs[z3_arg_name] = member_cls
            else:
                # use the default z3 constructor
                self.p4_attrs[z3_arg_name] = z3_member

            self.members[z3_arg_name] = member_constructor
        self.valid = z3.BoolVal(True)

    def bind(self, parent_const: z3.AstRef):
        members = []
        for member_name, member_constructor in self.members.items():
            # a z3 constructor dependent on the parent constant
            z3_member = member_constructor(parent_const)
            # retrieve the member we are accessing
            member = self.resolve_reference(member_name)
            if isinstance(member, P4ComplexInstance):
                # it is a complex type
                # propagate the parent constant to all children
                member.bind(z3_member)
            else:
                # a simple z3 type, just update the constructor
                self.set_or_add_var(member_name, z3_member)
            members.append(z3_member)

    def bind_to_name(self, name):
        for member_name, member_constructor in self.members.items():
            var_name = f"{name}.{member_name}"
            # retrieve the member we are accessing
            member = self.resolve_reference(member_name)
            member_type = member_constructor.range()
            if isinstance(member, P4ComplexInstance):
                # it is a complex type
                # propagate the parent constant to all children
                member.bind_to_name(var_name)
            else:
                # a simple z3 type, just update the constructor
                self.set_or_add_var(
                    member_name, z3.Const(var_name, member_type))

    def get_z3_repr(self) -> z3.DatatypeRef:
        ''' This method returns the current representation of the object in z3
        logic. Use the z3 constant variable of the object and propagate it
        through all its children.'''
        members = []

        for member_name, member_constructor in self.members.items():
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                # we have a complex type
                # retrieve the member and call the constructor
                # call the constructor of the complex type
                members.append(member_val.get_z3_repr())
            else:
                # if member_val.sort() != member_type:
                #     members.append(z3_cast(member_val, member_type))
                if self.valid == z3.BoolVal(False):
                    member_type = member_constructor.range()
                    member_val = z3.Const("invalid", member_type)
                # else:
                members.append(member_val)
        return self.z3_type.constructor(0)(*members)

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
                var = sub_class.p4_attrs[suffix]
            else:
                var = self.p4_attrs[var]
        return var

    def set_list(self, rvals):
        self.valid = z3.BoolVal(True)
        for idx, member in enumerate(self.members.items()):
            member_name = member[0]
            member_const = member[1]
            member_type = member_const.range()
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
        self._update_dict(lval, rval, self.p4_attrs)

    def sort(self):
        return self.z3_type

    def flatten(self, return_strings=False):
        members = []
        for member_name in self.members:
            member = self.resolve_reference(member_name)
            if isinstance(member, P4ComplexInstance):
                sub_members = member.flatten(return_strings)
                if return_strings:
                    for idx, sub_member in enumerate(sub_members):
                        merged_member = f"{member_name}.{sub_member}"
                        sub_members[idx] = merged_member
                members.extend(sub_members)
            else:
                if return_strings:
                    members.append(member_name)
                else:
                    members.append(member)
        return members

    def merge_attrs(self, cond, other_attrs):
        for attr_name, then_val in other_attrs.items():
            try:
                attr_val = self.resolve_reference(attr_name)
            except KeyError:
                # if the attribute does not exist it is not relevant
                # this is because of scoping
                # FIXME: Make sure this is actually the case...
                continue
            if isinstance(attr_val, P4ComplexInstance):
                attr_val.merge_attrs(cond, then_val.p4_attrs)
            elif isinstance(attr_val, z3.ExprRef):
                if then_val.sort() != attr_val.sort():
                    attr_val = z3_cast(attr_val, then_val.sort())
                if_expr = z3.simplify(z3.If(cond, then_val, attr_val))
                self.p4_attrs[attr_name] = if_expr

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result.p4_attrs = copy.copy(self.p4_attrs)
        for name, val in self.p4_attrs.items():
            if isinstance(val, P4ComplexInstance):
                result.p4_attrs[name] = copy.copy(val)
        return result

    def __repr__(self):
        ref_count = self.p4z3_type.ref_count
        return f"{self.__class__.__name__}_{ref_count}"

    def __eq__(self, other):
        # It can happen that we compare to a list
        # comparisons are almost the same just do not use members
        if isinstance(other, P4ComplexInstance):
            other_list = []
            for other_member_name in other.members:
                other_list.append(other.resolve_reference(other_member_name))
        elif isinstance(other, list):
            other_list = other
        else:
            return z3.BoolVal(False)

        # there is a mismatch in members, clearly not equal
        if len(self.members.keys()) != len(other_list):
            return z3.BoolVal(False)

        eq_members = []
        for index, self_member_name in enumerate(self.members):
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

    def propagate_validity_bit(self):
        # structs can be contained in headers so they can also be deactivated...
        for member_name in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.propagate_validity_bit()
        self.valid = z3.Bool(f"{self.name}_valid")


class StructType(P4ComplexType):

    def instantiate(self, name, parent_const=None):
        return StructInstance(name, self, parent_const)


class StructInstance(P4ComplexInstance):

    def __init__(self, name, p4z3_type, parent_const=None):
        super(StructInstance, self).__init__(name, p4z3_type, parent_const)
        self.var_buffer = {}

    def activate(self, label="undefined"):
        # structs may have headers that can be deactivated
        for member_name in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.activate()

    def deactivate(self, label="undefined"):
        # structs may have headers that can be deactivated
        for member_name in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.deactivate(label)


class HeaderType(StructType):

    def instantiate(self, name, parent_const=None):
        return HeaderInstance(name, self, parent_const)


class HeaderInstance(StructInstance):

    def __init__(self, name, p4z3_type, parent_const=None):
        super(HeaderInstance, self).__init__(name, p4z3_type, parent_const)
        self.valid = z3.BoolVal(True)
        self.p4_attrs["isValid"] = self.isValid
        self.p4_attrs["setValid"] = self.setValid
        self.p4_attrs["setInvalid"] = self.setInvalid
        self.union_parent = None

    def activate(self, label="undefined"):
        for member_name in self.members:
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
        for member_name in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, P4ComplexInstance):
                member_val.deactivate(label)
            else:
                member_type = member_val.sort()
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
            for member in union.members:
                member_hdr = union.resolve_reference(member)
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
            for member in union.members:
                member_hdr = union.resolve_reference(member)
                # check whether the header is the same object
                # any other header is now invalid
                member_hdr.deactivate()
        # This is a built-in
        self.deactivate()

    def bind_to_union(self, union_instance):
        # FIXME: This ignores copying
        # the reference in the parent will be stale
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
            return z3.Or(check_invalid, comparison)
        return super().__eq__(other)

    def __copy__(self):
        result = super(HeaderInstance, self).__copy__()
        # we need to update the reference of the function to the new object
        # quite nasty...
        result.p4_attrs["isValid"] = result.isValid
        result.p4_attrs["setValid"] = result.setValid
        result.p4_attrs["setInvalid"] = result.setInvalid
        return result


class HeaderUnionType(HeaderType):
    def instantiate(self, name, parent_const=None):
        return HeaderUnionInstance(name, self, parent_const)


class HeaderUnionInstance(HeaderInstance):

    def __init__(self, name, p4z3_type, parent_const=None):
        # TODO: Check if this class is implemented correctly...
        super(HeaderUnionInstance, self).__init__(
            name, p4z3_type, parent_const)
        for member in self.members:
            member_hdr = self.resolve_reference(member)
            member_hdr.bind_to_union(self)

    def isValid(self, p4_state=None):
        valid_list = []
        for member in self.members:
            member_hdr = self.resolve_reference(member)
            valid_list.append(member_hdr.isValid())
        return z3.Or(*valid_list)


class ListType(P4ComplexType):

    def __init__(self, name, z3_args):
        for idx, arg in enumerate(z3_args):
            z3_args[idx] = (f"{idx}", arg)
            # some little hack to automatically infer a random type name
            name += str(arg)
        super(ListType, self).__init__(name, z3_args)

    # TODO: Implement this class correctly...
    def instantiate(self, name, parent_const=None):
        return ListInstance(name, self, parent_const)


class ListInstance(P4ComplexInstance):

    def bind(self, parent_const: z3.AstRef):
        # Lists are static so they do not have variable types.
        pass


class HeaderStack(StructType):

    def __init__(self, name, z3_args):
        for idx, arg in enumerate(z3_args):
            z3_args[idx] = (f"{idx}", arg)
        super(HeaderStack, self).__init__(name, z3_args)

    # TODO: Implement this class correctly...
    def instantiate(self, name, parent_const=None):
        return HeaderStackInstance(name, self, parent_const)


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
                hdr = self.parent_hdr.p4_attrs[f"{self.parent_hdr.nextIndex}"]
            except KeyError:
                # if the header does not exist use it to break out of the loop?
                size = self.parent_hdr.p4_attrs["size"]
                hdr = self.parent_hdr.p4_attrs[f"{size -1}"]
            self.parent_hdr.nextIndex += 1
            self.parent_hdr.p4_attrs["lastIndex"] += 1
            return hdr
        if key == "last":
            # This is a built-in
            # TODO: Check if this implementation makes sense
            last = 0 if self.parent_hdr.p4_attrs["size"] < 1 else self.parent_hdr.p4_attrs["size"] - 1
            hdr = self.parent_hdr.p4_attrs[f"{last}"]
            return hdr

        val = dict.__getitem__(self, key)
        return val

    def __setitem__(self, key, val):
        dict.__setitem__(self, key, val)


class HeaderStackInstance(StructInstance):

    def __init__(self, name, p4z3_type, parent_const=None):
        super(HeaderStackInstance, self).__init__(
            name, p4z3_type, parent_const)

        # this is completely nuts but it works for now
        # no idea how to deal with properties
        # this intercepts dictionary lookups and modifies the header in place
        self.p4_attrs = HeaderStackDict(self.p4_attrs, self)
        self.nextIndex = 0
        self.p4_attrs["push_front"] = self.push_front
        self.p4_attrs["pop_front"] = self.pop_front
        self.p4_attrs["size"] = len(self.members)
        self.p4_attrs["lastIndex"] = z3.BitVecVal(self.nextIndex, 32) - 1

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
            hdr = self.p4_attrs[f"{self.nextIndex}"]
        except KeyError:
            # if the header does not exist use it to break out of the loop?
            size = self.p4_attrs["size"]
            hdr = self.p4_attrs[f"{size -1}"]
        self.nextIndex += 1
        self.p4_attrs["lastIndex"] += 1
        return hdr

    @property
    def last(self):
        # This is a built-in
        # TODO: Check if this implementation makes sense
        last = 0 if self.p4_attrs["size"] < 1 else self.p4_attrs["size"] - 1
        hdr = self.p4_attrs[f"{last}"]
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
        result.p4_attrs["push_front"] = result.push_front
        result.p4_attrs["pop_front"] = result.pop_front
        return result


class Enum(P4ComplexInstance):

    def __init__(self, name, z3_args, parent_const=None):
        self.p4_attrs = {}
        self.name = name
        self.z3_type = z3.BitVecSort(32)
        for idx, enum_name in enumerate(z3_args):
            self.p4_attrs[enum_name] = z3.BitVecVal(idx, 32)
        self.z3_args = z3_args

    def instantiate(self, name, parent_const=None):
        return self

    def bind(self, parent_const: z3.AstRef):
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
            log.warning("Enum: Comparison to %s of type %s not supported",
                        other, type(other))
            return z3.BoolVal(False)


class SerEnum(Enum):

    def __init__(self, name, z3_args, z3_type):
        self.arg_vals = []
        self.name = name
        self.z3_type = z3_type
        self.p4_attrs = {}
        self.members = OrderedDict()
        for z3_arg in z3_args:
            z3_arg_name = z3_arg[0]
            z3_arg_val = z3_arg[1]
            self.p4_attrs[z3_arg_name] = z3_arg_val

    def instantiate(self, name, parent_const=None):
        return self


class P4Extern(P4ComplexInstance):
    def __init__(self, name, type_params=[], methods=[]):
        # Externs are this weird bastard child of callables and a complex type
        # FIXME: Unify types
        z3_type = z3.Datatype(name)
        z3_type.declare(f"mk_{name}")
        self.members = OrderedDict()
        self.z3_type = z3_type.create()
        self.const = z3.Const(name, self.z3_type)
        self.p4_attrs = {}
        # simple fix for now until I know how to initialize params for externs
        self.params = {}
        self.name = name
        self.type_params = type_params
        # these are method declarations, not methods
        for method in methods:
            self.p4_attrs[method.lval] = method.rval

    def init_type_params(self, *args, **kwargs):
        # the extern is instantiated, we need to copy it
        init_extern = self.initialize()
        for idx, t_param in enumerate(init_extern.type_params):
            for method in init_extern.p4_attrs.values():
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


class P4State(P4ComplexType):
    # TODO: Implement this class correctly...
    def instantiate(self, name, global_values, instances):
        return P4StateInstance(name, self, global_values, instances)


class P4StateInstance(P4ComplexInstance):
    """
    A P4State Object is a special, dynamic type of P4ComplexType. It represents
    the execution environment and its z3 representation is ultimately used to
    compare different programs. P4State is mostly just a wrapper for all inout
    values. It also manages the execution chain of the program.
    """

    def __init__(self, name, p4z3_type, global_values, instances):
        # deques allow for much more efficient pop and append operations
        # this is all we do so this works well
        super(P4StateInstance, self).__init__(name, p4z3_type)
        self.expr_chain = deque()
        self.globals = global_values
        self.locals = self.p4_attrs
        for instance_name, instance_val in instances.items():
            self.set_or_add_var(instance_name, instance_val)

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
        self._update_dict(lval, rval, self.locals)

    def resolve_reference(self, var):
        if isinstance(var, P4Member):
            var = var.eval(self)
        log.debug("Resolving reference %s", var)
        if isinstance(var, str):
            sub_class = self
            if '.' in var:
                # this means we are accessing a complex member
                # get the parent class and update its value
                prefix, suffix = var.rsplit(".", 1)
                # prefix may be a pointer to an actual complex type, resolve it
                sub_class = self.resolve_reference(prefix)
                var = sub_class.p4_attrs[suffix]
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
        chain = self.copy_expr_chain()
        return var_store, chain

    def restore(self, var_store, chain=None):
        for attr_name, attr_val in var_store.items():
            self.locals[attr_name] = attr_val
        if chain:
            self.expr_chain = chain

    def clear_expr_chain(self):
        self.expr_chain.clear()

    def clear_locals(self):
        self.locals.clear()

    def copy_expr_chain(self):
        return self.expr_chain.copy()

    def set_expr_chain(self, expr_chain):
        self.expr_chain = deque(expr_chain)

    def insert_exprs(self, exprs):
        if isinstance(exprs, list):
            self.expr_chain.extendleft(reversed(exprs))
        else:
            self.expr_chain.appendleft(exprs)

    class P4End(P4Z3Class):
        ''' This function is a little trick to ensure that chains are executed
            appropriately. When we reach the end of an execution chain, this
            expression returns the state of the program at the end of this
            particular chain.'''
        @staticmethod
        def eval(p4_state):
            return p4_state.get_z3_repr()

    def pop_next_expr(self):
        if self.expr_chain:
            return self.expr_chain.popleft()
        return self.P4End()

    def merge_attrs(self, cond, other_attrs):
        for attr_name, attr_val in self.locals.items():
            try:
                then_val = other_attrs[attr_name]
            except KeyError:
                # if the attribute does not exist it is not relevant
                # this is because of scoping
                # FIXME: Make sure this is actually the case...
                continue
            if isinstance(attr_val, P4ComplexInstance):
                attr_val.merge_attrs(cond, then_val.p4_attrs)
            elif isinstance(attr_val, z3.ExprRef):
                if then_val.sort() != attr_val.sort():
                    attr_val = z3_cast(attr_val, then_val.sort())
                if_expr = z3.simplify(z3.If(cond, then_val, attr_val))
                self.locals[attr_name] = if_expr


class Z3Reg():
    def __init__(self):
        self._types = {}
        self._globals = {}

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
            self._globals[name] = p4_class.initialize()
        elif isinstance(p4_class, (Enum)):
            # enums are special static types
            # we need to add them to the list of accessible variables
            # and their type is actually the z3 type, not the class type
            name = p4_class.name
            self._globals[name] = p4_class
            self._types[name] = p4_class.z3_type
        elif isinstance(p4_class, P4Declaration):
            # FIXME: Typedefs should not be added here
            name = p4_class.lval
            self._globals[name] = p4_class.rval
            self._types[name] = p4_class.rval
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
        instance_name = f"{name}"
        p4_state = P4State(name, stripped_args).instantiate(
            instance_name, self._globals, instances)
        p4_state.propagate_validity_bit()
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
