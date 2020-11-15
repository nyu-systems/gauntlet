from collections import deque
import types
import copy

import z3
from p4z3.base import log
from p4z3.base import StaticType, P4Z3Class, P4Expression
from p4z3.base import P4Slice, P4ComplexType, P4Member
from p4z3.base import StructInstance, P4ComplexInstance, HeaderStack
from p4z3.base import propagate_validity_bit, resolve_type, z3_cast
from p4z3.base import gen_instance, TypeDeclaration, Enum
from p4z3.base import P4Extern, P4Declaration, ControlDeclaration

from p4z3.z3int import Z3Int


class P4Context(P4Z3Class):

    def __init__(self, parent_context, var_buffer):
        self.parent_context = parent_context
        self.var_buffer = var_buffer
        self.has_returned = False
        # to merge the return exprs after a callable has completed
        self.return_exprs = deque()
        # to merge all the return states after a callable has completed
        self.return_states = deque()
        # this can be used to perform return casts in the current context
        self.return_type = None
        self.forward_conds = deque()
        self.tmp_forward_cond = z3.BoolVal(True)
        self.locals = {}
        self.type_map = {}

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
        for par_name, (mode, par_ref, par_val) in self.var_buffer.items():
            # we retrieve the current value
            val = p4_state.resolve_reference(par_name)

            # we then reset the name in the scope to its original
            log.debug("Resetting %s to %s", par_name, type(par_val))
            # value has not existed previously, ignore
            if par_val is not None:
                p4_state.set_or_add_var(par_name, par_val)

            # if the param was copy-out, we copy the value we retrieved
            # back to the original input reference
            if mode in ("inout", "out"):
                log.debug("Copy-out: %s to %s", val, par_ref)
                # copy it back to the input reference
                # this assumes an lvalue as input
                p4_state.set_or_add_var(par_ref, val)

    def resolve_expr(self, p4_state, expr):
        # Resolves to z3 and z3p4 expressions
        # ints, lists, and dicts are also okay

        # resolve potential string references first
        log.debug("Resolving %s", expr)
        if isinstance(expr, str):
            expr = p4_state.resolve_reference(expr)
        if isinstance(expr, P4Expression):
            # We got a P4 expression, recurse and resolve...
            expr = expr.eval(p4_state)
            return p4_state.resolve_expr(expr)
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
                rval_expr = p4_state.resolve_expr(val_expr)
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

    def set_slice(self, p4_state, lval, rval):
        slice_l = p4_state.resolve_expr(lval.slice_l)
        slice_r = p4_state.resolve_expr(lval.slice_r)
        lval = lval.val
        lval, slice_l, slice_r = self.find_nested_slice(lval, slice_l, slice_r)

        # need to resolve everything first, these can be members
        lval_expr = p4_state.resolve_expr(lval)

        # z3 requires the extract value to be a bitvector, so we must cast ints
        # actually not sure where this could happen...
        if isinstance(lval_expr, int):
            lval_expr = lval_expr.as_bitvec

        rval_expr = p4_state.resolve_expr(rval)

        lval_expr_max = lval_expr.size() - 1
        if slice_l == lval_expr_max and slice_r == 0:
            # slice is full lval, nothing to do
            p4_state.set_or_add_var(lval, rval_expr)
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
        p4_state.set_or_add_var(lval, rval_expr)
        return

    def find_context(self, var):
        context = self
        while context is not None:
            try:
                return context, context.locals[var]
            except KeyError:
                context = context.parent_context
                continue
        # nothing found, empty result
        return None, None

    def set_or_add_var(self, p4_state, lval, rval, new_decl=False):
        if isinstance(lval, P4Slice):
            self.set_slice(p4_state, lval, rval)
            return
        if isinstance(lval, P4Member):
            lval.set_value(p4_state, rval)
            return
        # now that all the preprocessing is done we can assign the value
        log.debug("Setting %s(%s) to %s(%s) ",
                  lval, type(lval), rval, type(rval))
        context, lval_val = self.find_context(lval)
        if not context or new_decl:
            context = self

        # rvals could be a list, unroll the assignment
        if isinstance(rval, list) and lval_val is not None:
            if isinstance(lval_val, StructInstance):
                lval_val.set_list(rval)
            else:
                raise TypeError(
                    f"set_list {type(lval)} not supported!")
            return
        context.locals[lval] = rval

    def resolve_reference(self, p4_state, var):
        if isinstance(var, P4Member):
            return var.eval(p4_state)
        if isinstance(var, str):
            context, val = self.find_context(var)
            if not context:
                raise RuntimeError(f"Variable {var} not found!")
            return val
        return var

    def get_type(self, type_name):
        context = self
        while context is not None:
            try:
                return context.type_map[type_name]
            except KeyError:
                context = context.parent_context
                continue
        # nothing found, empty result
        raise KeyError

    def add_type(self, type_name, type_val):
        self.type_map[type_name] = type_val


class P4State():
    """
    A P4State Object is a special, dynamic type of P4ComplexType. It represents
    the execution environment and its z3 representation is ultimately used to
    compare different programs. P4State is mostly just a wrapper for all inout
    values. It also manages the execution chain of the program.
    """

    def __init__(self, extern_extensions):
        self.extern_extensions = extern_extensions
        self.name = "init_state"
        self.static_context = P4Context(None, {})
        # deques allow for much more efficient pop and append operations
        # this is all we do so this works well
        self.contexts = deque()
        self.exit_states = deque()
        self.has_exited = False
        self.flat_names = []
        self.members = {}
        self.z3_type = None
        self.const = None

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
        state_context = P4Context(self.current_context(), {})
        self.contexts.append(state_context)

        for instance_name, instance_val in instances.items():
            state_context.set_or_add_var(self, instance_name, instance_val)

        flat_args = []
        idx = 0
        for z3_arg_name, z3_arg_type in z3_args:
            z3_arg_type = resolve_type(self, z3_arg_type)
            if isinstance(z3_arg_type, P4ComplexType):
                member_cls = z3_arg_type.instantiate(f"{name}.{idx}")
                propagate_validity_bit(member_cls)
                for sub_member in z3_arg_type.flat_names:
                    flat_args.append((str(idx), sub_member.p4_type))
                    self.flat_names.append(
                        P4Member(z3_arg_name, sub_member.name))
                    idx += 1
                # this is a complex datatype, create a P4ComplexType
                state_context.set_or_add_var(
                    self, z3_arg_name, member_cls, True)
            else:
                flat_args.append((str(idx), z3_arg_type))
                self.flat_names.append(z3_arg_name)
                idx += 1
        z3_type = z3.Datatype(name)
        z3_type.declare(f"mk_{name}", *flat_args)
        self.z3_type = z3_type.create()

        self.const = z3.Const(name, self.z3_type)

        for type_idx, arg_name in enumerate(self.flat_names):
            member_constructor = self.z3_type.accessor(0, type_idx)
            state_context.set_or_add_var(
                self, arg_name, member_constructor(self.const), True)

    def get_type(self, type_name):
        context = self.current_context()
        return context.get_type(type_name)

    def current_context(self):
        if self.contexts:
            return self.contexts[-1]
        else:
            return self.static_context

    def resolve_reference(self, ref_name):
        context = self.current_context()
        return context.resolve_reference(self, ref_name)

    def resolve_expr(self, ref_name):
        context = self.current_context()
        return context.resolve_expr(self, ref_name)

    def set_or_add_var(self, lval, rval, new_decl=False):
        context = self.current_context()
        return context.set_or_add_var(self, lval, rval, new_decl)

    def get_members(self):
        ''' This method returns the current representation of the object in z3
        logic. This function has a side-effect, validity may be modified.'''
        members = []
        for member_name, _ in self.members:
            member_val = self.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                # first we need to make sure that validity is correct
                members.extend(member_val.flatten(None))
            else:
                members.append(member_val)
        return members

    def get_z3_repr(self):
        return self.z3_type.constructor(0)(*self.get_members())

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
                if isinstance(attr_val, StructInstance):
                    attr_val = copy.copy(attr_val)
                attr_copy[attr_name] = attr_val
        return attr_copy

    def checkpoint(self):
        var_store = self.copy_attrs()
        contexts = self.contexts.copy()
        return var_store, contexts

    def restore(self, var_store, contexts=None):
        for attr_name, attr_val in var_store.items():
            self.set_or_add_var(attr_name, attr_val)
        if contexts:
            self.contexts = contexts

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
            rval = p4_class.compute_rval(self)
            self.declare_var(name, rval)
        else:
            raise RuntimeError(
                "Unsupported global declaration %s" % type(p4_class))

    def declare_var(self, lval, rval):
        self.static_context.locals[lval] = rval

    def declare_type(self, lval, rval):
        self.static_context.add_type(lval, rval)

    def set_context(self, name, p4_params):
        stripped_args = []
        instances = {}
        for extern_set in self.extern_extensions:
            for extern_name, extern in extern_set.items():
                self.declare_type(extern_name, extern)
        for param in p4_params:
            p4_type = resolve_type(self, param.p4_type)
            if param.mode in ("inout", "out"):
                # only inouts or outs matter as output
                stripped_args.append((param.name, p4_type))
            else:
                # for other inputs we can instantiate something
                instance = gen_instance(self, param.name, p4_type)
                instances[param.name] = instance
        self.set_datatype(name, stripped_args, instances)
        return self

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
        if "main" in self.static_context.locals:
            return self.static_context.locals["main"]
        return None
