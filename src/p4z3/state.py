from collections import deque
import types
import copy

import z3
from p4z3.base import log
from p4z3.base import StaticType, P4Z3Class, P4Expression
from p4z3.base import P4Slice, P4ComplexType, P4Member
from p4z3.base import StructInstance, P4ComplexInstance, HeaderStack
from p4z3.base import z3_cast, propagate_validity_bit
from p4z3.base import TypeDeclaration, Enum
from p4z3.base import P4Extern, P4Declaration, ControlDeclaration

from p4z3.z3int import Z3Int


class TypeSpecializer():
    def __init__(self, p4z3_type, *args):
        self.p4z3_type = p4z3_type
        self.args = args

    def eval(self, ctx):
        p4z3_type = ctx.resolve_type(self.p4z3_type)
        type_ctx = LocalContext(ctx, {})
        return p4z3_type.init_type_params(type_ctx, *self.args)


class P4Context():

    def __init__(self):
        self.locals = {}
        self.type_map = {}

    def find_context(self, var):
        raise NotImplementedError("Method find_context not implemented!")

    def resolve_type(self, type_name):
        raise NotImplementedError("Method resolve_type not implemented!")

    def gen_instance(self, var_name, p4z3_type):
        p4z3_type = self.resolve_type(p4z3_type)
        if isinstance(p4z3_type, P4ComplexType):
            z3_cls = p4z3_type.instantiate(var_name)
            # this instance is fresh, so bind to itself
            z3_cls.bind(z3_cls.const)
            return z3_cls
        elif isinstance(p4z3_type, StaticType):
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

    def resolve_expr(self, expr):
        # Resolves to z3 and z3p4 expressions
        # ints and lists  are also okay

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
        if isinstance(expr, (StaticType, P4ComplexInstance, P4Z3Class, types.MethodType)):
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

    def set_slice(self, ctx, lval, rval):
        slice_l = ctx.resolve_expr(lval.slice_l)
        slice_r = ctx.resolve_expr(lval.slice_r)
        lval = lval.val
        lval, slice_l, slice_r = self.find_nested_slice(lval, slice_l, slice_r)

        # need to resolve everything first, these can be members
        lval_expr = ctx.resolve_expr(lval)

        # z3 requires the extract value to be a bitvector, so we must cast ints
        # actually not sure where this could happen...
        if isinstance(lval_expr, int):
            lval_expr = lval_expr.as_bitvec

        rval_expr = ctx.resolve_expr(rval)

        lval_expr_max = lval_expr.size() - 1
        if slice_l == lval_expr_max and slice_r == 0:
            # slice is full lval, nothing to do
            ctx.set_or_add_var(lval, rval_expr)
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
        ctx.set_or_add_var(lval, rval_expr)
        return

    def set_or_add_var(self, lval, rval, new_decl=False):
        if isinstance(lval, P4Slice):
            self.set_slice(self, lval, rval)
            return
        if isinstance(lval, P4Member):
            lval.set_value(self, rval)
            return
        # now that all the preprocessing is done we can assign the value
        log.debug("Setting %s(%s) to %s(%s) ",
                  lval, type(lval), rval, type(rval))
        ctx, lval_val = self.find_context(lval)
        if new_decl or not ctx:
            ctx = self

        # rvals could be a list, unroll the assignment
        if isinstance(rval, list) and lval_val is not None:
            if isinstance(lval_val, StructInstance):
                lval_val.set_list(rval)
            elif isinstance(lval, str):
                # TODO: Decide whether this makes sense
                log.warning("Skipping assignment %s to %s", rval, lval)
            else:
                raise TypeError(
                    f"set_list {type(lval)} not supported!")
            return
        ctx.locals[lval] = rval

    def resolve_reference(self, var):
        if isinstance(var, P4Member):
            return var.eval(self)
        if isinstance(var, str):
            ctx, val = self.find_context(var)
            if not ctx:
                raise RuntimeError(f"Variable {var} not found!")
            return val
        return var

    def add_type(self, type_name, type_val):
        self.type_map[type_name] = type_val


class StaticContext(P4Context):
    def __init__(self):
        super(StaticContext, self).__init__()
        self.extern_extensions = {}
        self.master_ctx = self
        self.p4_state = None
        self.parent_ctx = None

    def add_extern_extensions(self, extern_extensions):
        self.extern_extensions = {
            **self.extern_extensions, **extern_extensions}

    def get_extern_extensions(self):
        return self.extern_extensions

    def declare_global(self, p4_class):
        if isinstance(p4_class, (P4ComplexType, P4Extern)):
            name = p4_class.name
            self.add_type(name, p4_class)
        elif isinstance(p4_class, TypeDeclaration):
            p4_type = self.resolve_type(p4_class.p4_type)
            self.add_type(p4_class.name, p4_type)
        elif isinstance(p4_class, ControlDeclaration):
            self.set_or_add_var(p4_class.ctrl.name, p4_class.ctrl)
            self.add_type(p4_class.ctrl.name, p4_class.ctrl)
        elif isinstance(p4_class, Enum):
            # enums are special static types
            # we need to add them to the list of accessible variables
            # and their type is actually the z3 type, not the class type
            name = p4_class.name
            self.set_or_add_var(name, p4_class)
            p4_type = self.resolve_type(p4_class.z3_type)
            self.add_type(name, p4_type)
        elif isinstance(p4_class, P4Declaration):
            name = p4_class.lval
            rval = p4_class.compute_rval(self)
            self.set_or_add_var(name, rval)
        else:
            raise RuntimeError(
                "Unsupported global declaration %s" % type(p4_class))

    def stack(self, z3_type, num):
        # Header stacks are a bit special because they are basically arrays
        # with specific features
        # We need to declare a new z3 type and add a new complex class
        name = f"{z3_type}{num}"
        p4_stack = HeaderStack(name, self, [z3_type] * num)
        self.declare_global(p4_stack)
        return self.resolve_type(name)

    def get_value(self, expr):
        val = self.resolve_expr(expr)
        if isinstance(val, z3.BitVecNumRef):
            # unfortunately, we need to get the real int value here
            val = Z3Int(val.as_long(), val.size())
        return val

    def get_main_function(self):
        if "main" in self.locals:
            return self.locals["main"]
        return None

    def resolve_type(self, type_name):
        if isinstance(type_name, str):
            return self.type_map[type_name]
        if isinstance(type_name, TypeSpecializer):
            return type_name.eval(self)
        return type_name

    def find_context(self, var):
        ctx = self
        try:
            return ctx, ctx.locals[var]
        except KeyError:
            ctx = ctx.parent_ctx
        # nothing found, empty result
        return None, None


class LocalContext(P4Context):
    def __init__(self, parent_ctx, var_buffer):
        super(LocalContext, self).__init__()
        self.parent_ctx = parent_ctx
        self.master_ctx = parent_ctx.master_ctx
        self.var_buffer = var_buffer
        self.has_returned = False
        # to merge the return exprs after a callable has completed
        self.return_exprs = deque()
        # to merge all the return states after a callable has completed
        self.return_states = deque()
        # this can be used to perform return casts in the current ctx
        self.return_type = None
        self.forward_conds = deque()
        self.tmp_forward_cond = z3.BoolVal(True)

    def add_to_buffer(self, var_dict):
        self.var_buffer = {**self.var_buffer, **var_dict}

    def prepend_to_buffer(self, var_dict):
        self.var_buffer = {**var_dict, **self.var_buffer}

    def declare_var(self, lval, rval):
        self.locals[lval] = rval

    def copy_out(self, ctx):
        # restore any variables that may have been overridden
        # with copy-out we copy from left to right
        # values on the right override values on the left
        # the var buffer is an ordered dict that maintains this order
        for par_name, (mode, par_ref, par_val) in self.var_buffer.items():
            # we retrieve the current value
            val = self.resolve_reference(par_name)

            # we then reset the name in the scope to its original
            log.debug("Resetting %s to %s", par_name, type(par_val))
            # value has not existed previously, ignore
            if par_val is not None:
                ctx.set_or_add_var(par_name, par_val)

            # if the param was copy-out, we copy the value we retrieved
            # back to the original input reference
            if mode in ("inout", "out"):
                log.debug("Copy-out: %s to %s", val, par_ref)
                # copy it back to the input reference
                # this assumes an lvalue as input
                ctx.set_or_add_var(par_ref, val)

    def get_p4_state(self):
        return self.master_ctx.p4_state

    def set_p4_state(self, p4_state):
        self.master_ctx.p4_state = p4_state

    def add_extern_extensions(self, extern_extensions):
        self.master_ctx.add_extern_extensions(extern_extensions)

    def get_extern_extensions(self):
        return self.master_ctx.get_extern_extensions()

    def get_attrs(self):
        attr_dict = {}
        ctx = self
        while not isinstance(ctx, StaticContext):
            for attr_name, var_val in ctx.locals.items():
                if attr_name not in attr_dict:
                    attr_dict[attr_name] = var_val
            ctx = ctx.parent_ctx
        return attr_dict

    def copy_attrs(self):
        attr_copy = {}
        ctx = self
        # copy everything except the first ctx, which are the global values
        while not isinstance(ctx, StaticContext):
            for attr_name, attr_val in ctx.locals.items():
                if attr_name not in attr_copy:
                    if isinstance(attr_val, StructInstance):
                        attr_val = copy.copy(attr_val)
                    attr_copy[attr_name] = attr_val
            ctx = ctx.parent_ctx
        return attr_copy

    def checkpoint(self):
        var_store = self.copy_attrs()
        return var_store

    def restore(self, var_store):
        for attr_name, attr_val in var_store.items():
            self.set_or_add_var(attr_name, attr_val)

    def set_exited(self, exit_state):
        self.master_ctx.p4_state.has_exited = exit_state

    def get_exited(self):
        return self.master_ctx.p4_state.has_exited

    def add_exit_state(self, cond, exit_state):
        self.master_ctx.p4_state.exit_states.append((cond, exit_state))

    def get_exit_states(self):
        return self.master_ctx.p4_state.exit_states

    def resolve_type(self, type_name):
        ctx = self
        if isinstance(type_name, TypeSpecializer):
            return type_name.eval(ctx)
        if isinstance(type_name, str):
            while not isinstance(ctx, StaticContext):
                try:
                    return ctx.type_map[type_name]
                except KeyError:
                    ctx = ctx.parent_ctx
                    continue
            # try the static ctx
            return ctx.type_map[type_name]
        return type_name

    def find_context(self, var):
        ctx = self
        while not isinstance(ctx, StaticContext):
            try:
                return ctx, ctx.locals[var]
            except KeyError:
                ctx = ctx.parent_ctx
                continue
        # try the static ctx
        try:
            return ctx, ctx.locals[var]
        except KeyError:
            # nothing found, empty result
            return None, None

class P4State():

    def __init__(self, name, members):
        self.name = name
        self.members = members
        # deques allow for much more efficient pop and append operations
        # this is all we do so this works well
        self.flat_names = []
        self.z3_type = None
        self.const = None

        # keep track of exit states and conditions
        self.exit_states = deque()
        self.has_exited = False

    def initialize(self, ctx):
        flat_args = []
        idx = 0
        for z3_arg_name, z3_arg_type in self.members:
            z3_arg_type = ctx.resolve_type(z3_arg_type)
            if isinstance(z3_arg_type, P4ComplexType):
                member_cls = z3_arg_type.instantiate(f"{self.name}.{idx}")
                propagate_validity_bit(member_cls)
                for sub_member in z3_arg_type.flat_names:
                    flat_args.append((str(idx), sub_member.p4_type))
                    self.flat_names.append(
                        P4Member(z3_arg_name, sub_member.name))
                    idx += 1
                # this is a complex datatype, create a P4ComplexType
                ctx.set_or_add_var(z3_arg_name, member_cls, True)
            else:
                flat_args.append((str(idx), z3_arg_type))
                self.flat_names.append(z3_arg_name)
                idx += 1
        z3_type = z3.Datatype(self.name)
        z3_type.declare(f"mk_{self.name}", *flat_args)
        self.z3_type = z3_type.create()
        self.const = z3.Const(self.name, self.z3_type)

        for type_idx, arg_name in enumerate(self.flat_names):
            member_constructor = self.z3_type.accessor(0, type_idx)
            ctx.set_or_add_var(
                arg_name, member_constructor(self.const), True)

    def get_members(self, ctx):
        ''' This method returns the current representation of the object in z3
        logic. This function has a side-effect, validity may be modified.'''
        members = []
        for member_name, _ in self.members:
            member_val = ctx.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                # first we need to make sure that validity is correct
                members.extend(member_val.flatten(None))
            else:
                members.append(member_val)
        return members

    def get_z3_repr(self, ctx):
        return self.z3_type.constructor(0)(*self.get_members(ctx))

    def create_z3_representation(self, ctx):
        members = self.get_members(ctx)
        # and also merge back all the exit states we collected
        for exit_cond, exit_state in reversed(ctx.get_exit_states()):
            for idx, exit_member in enumerate(exit_state):
                members[idx] = z3.If(exit_cond, exit_member, members[idx])
        return self.z3_type.constructor(0)(*members)
