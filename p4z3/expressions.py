from copy import deepcopy
from collections import OrderedDict
import operator as op
import z3

import p4z3.base as base
from p4z3.base import log


def resolve_expr(p4_state, expr):
    # Resolves to z3 and z3p4 expressions, ints, lists, and dicts are also okay
    # resolve potential string references first
    log.debug("Resolving %s", expr)
    if isinstance(expr, str):
        val = p4_state.resolve_reference(expr)
        if val is None:
            raise RuntimeError(f"Value {expr} could not be found!")
    else:
        val = expr
    if isinstance(val, (z3.ExprRef, int)):
        # These are z3 types and can be returned
        # Unfortunately int is part of it because z3 is very inconsistent
        # about var handling...
        return val
    if isinstance(val, base.P4ComplexType):
        # If we get a whole class return the object
        # Do not return the z3 type because we may assign a complete structure
        return val
    if isinstance(val, P4Z3Class):
        # We got a P4 type, recurse...
        val = val.eval(p4_state)
        return resolve_expr(p4_state, val)
    if isinstance(val, list):
        # For lists, resolve each value individually and return a new list
        list_expr = []
        for val_expr in val:
            rval_expr = resolve_expr(p4_state, val_expr)
            list_expr.append(rval_expr)
        return list_expr
    if isinstance(val, dict):
        # For dicts, resolve each value individually and return a new dict
        dict_expr = []
        for name, val_expr in val.items():
            rval_expr = resolve_expr(p4_state, val_expr)
            dict_expr[name] = rval_expr
        return dict_expr
    raise TypeError(f"Value of type {type(val)} cannot be resolved!")


def resolve_action(action_expr):
    # TODO Fix this roundabout way of getting a P4 Action, super annoying...
    if isinstance(action_expr, MethodCallExpr):
        action_name = action_expr.p4_method
        action_args = action_expr.args
    elif isinstance(action_expr, str):
        action_name = action_expr
        action_args = []
    else:
        raise TypeError(
            f"Expected a method call, got {type(action_name)}!")
    return action_name, action_args


def get_type(p4_state, expr):
    ''' Return the type of an expression, Resolve, if needed'''
    arg_expr = resolve_expr(p4_state, expr)
    if isinstance(arg_expr, base.P4ComplexType):
        arg_type = arg_expr.get_z3_repr().sort()
    else:
        arg_type = arg_expr.sort()
    return arg_type


def z3_implies(p4_state, cond, then_expr):
    no_match = base.step(p4_state)
    return z3.If(cond, then_expr, no_match)


def check_bool(expr):
    if isinstance(expr, z3.BoolRef):
        # Convert boolean variables to a bit vector representation
        # TODO: Make all bools a bitvector of size 1
        expr = z3.If(expr, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
    return expr


def check_enum(expr):
    if isinstance(expr, base.Enum):
        expr = expr.get_z3_repr()
    return expr


def align_bitvecs(bitvec1, bitvec2, p4_state):
    if isinstance(bitvec1, z3.BitVecRef) and isinstance(bitvec2, z3.BitVecRef):
        if bitvec1.size() < bitvec2.size():
            bitvec1 = P4Cast(bitvec1, bitvec2).eval(p4_state)
        if bitvec1.size() > bitvec2.size():
            bitvec2 = P4Cast(bitvec2, bitvec1).eval(p4_state)
    return bitvec1, bitvec2


class P4Z3Class():
    def eval(self, p4_state):
        raise NotImplementedError("Method eval not implemented!")


class P4Op(P4Z3Class):
    def get_value():
        raise NotImplementedError("get_value")

    def eval(self, p4_state):
        raise NotImplementedError("eval")


class P4BinaryOp(P4Op):
    def __init__(self, lval, rval, operator):
        self.lval = lval
        self.rval = rval
        self.operator = operator

    def get_value(self):
        # TODO: This is a kind of hacky function to work around bitvectors
        # There must be a better way to implement this
        lval = self.lval
        rval = self.rval
        if isinstance(lval, P4Op):
            lval = lval.get_value()
        if isinstance(rval, P4Op):
            rval = rval.get_value()
        if isinstance(lval, int) and isinstance(rval, int):
            return self.operator(lval, rval)
        else:
            raise RuntimeError(
                f"Operations on {lval} or {rval} not supported!")

    def eval(self, p4_state):
        lval_expr = resolve_expr(p4_state, self.lval)
        rval_expr = resolve_expr(p4_state, self.rval)

        # if we have enums, do not use them for operations
        # for some reason, overloading equality does not work here...
        # instead use their current representation...
        lval_expr = check_enum(lval_expr)
        rval_expr = check_enum(rval_expr)
        lval_expr, rval_expr = align_bitvecs(
            lval_expr, rval_expr, p4_state)
        return self.operator(lval_expr, rval_expr)


class P4UnaryOp(P4Op):
    def __init__(self, val, operator):
        self.val = val
        self.operator = operator

    def get_value(self):
        val = self.val
        if isinstance(val, P4Op):
            val = val.get_value()
        if isinstance(val, int):
            return self.operator(val)
        else:
            raise RuntimeError(f"Operations on {val}not supported!")

    def eval(self, p4_state):
        expr = resolve_expr(p4_state, self.val)
        return self.operator(expr)


class P4not(P4UnaryOp):
    def __init__(self, val):
        operator = z3.Not
        P4UnaryOp.__init__(self, val, operator)


class P4abs(P4UnaryOp):
    def __init__(self, val):
        operator = op.abs
        P4UnaryOp.__init__(self, val, operator)


class P4inv(P4UnaryOp):
    def __init__(self, val):
        operator = op.inv
        P4UnaryOp.__init__(self, val, operator)


class P4neg(P4UnaryOp):
    def __init__(self, val):
        operator = op.neg
        P4UnaryOp.__init__(self, val, operator)


class P4add(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.add
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4sub(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.sub
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4addsat(P4BinaryOp):
    # TODO: Not sure if this is right, check eventually
    def __init__(self, lval, rval):
        operator = (lambda x, y: z3.BVAddNoOverflow(x, y, False))
        operator = op.add
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4subsat(P4BinaryOp):
    # TODO: Not sure if this is right, check eventually
    def __init__(self, lval, rval):
        operator = (lambda x, y: z3.BVSubNoUnderflow(x, y, False))
        operator = op.sub
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4mul(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.mul
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4mod(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.mod
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4pow(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.pow
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4band(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.and_
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4bor(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.or_
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4land(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = z3.And
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lor(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = z3.Or
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4xor(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.xor
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4div(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.truediv
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lshift(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.lshift
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4rshift(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.rshift
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lt(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.lt
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4le(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.le
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4eq(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.eq
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4ne(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.ne
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4ge(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.ge
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4gt(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.gt
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4Mask(P4BinaryOp):
    # TODO: Check if this mask operator is right
    def __init__(self, lval, rval):
        operator = op.and_
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4Slice(P4Z3Class):
    def __init__(self, val, slice_l, slice_r):
        self.val = val
        self.slice_l = slice_l
        self.slice_r = slice_r

    def eval(self, p4_state):
        val_expr = resolve_expr(p4_state, self.val)
        return z3.Extract(self.slice_l, self.slice_r, val_expr)


class P4Concat(P4Z3Class):
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_state):
        lval_expr = resolve_expr(p4_state, self.lval)
        rval_expr = resolve_expr(p4_state, self.rval)
        return z3.Concat(lval_expr, rval_expr)


class P4Member(P4Z3Class):

    def __new__(cls, lval, member):
        cls.lval = lval
        cls.member = member
        return f"{lval}.{member}"

    def eval(cls, p4_state):
        # lval_expr = resolve_expr(p4_state, cls.lval)
        # return getattr(lval_expr, cls.member)
        if isinstance(cls.lval, P4Z3Class):
            lval = cls.lval.eval(p4_state)
        else:
            lval = cls.lval
        if isinstance(cls.member, P4Z3Class):
            member = cls.member.eval(p4_state)
        else:
            member = cls.member
        return f"{lval}.{member}"


class P4Index(P4Z3Class):
    def __new__(cls, lval, index):
        cls.lval = lval
        cls.index = index
        return f"{lval}.{index}"

    def eval(cls, p4_state):
        lval_expr = resolve_expr(p4_state, cls.lval)
        index = resolve_expr(p4_state, cls.index)
        expr = lval_expr.get_var(str(index))
        return expr


class P4Path(P4Z3Class):
    def __init__(self, val):
        self.val = val

    def eval(self, p4_state):
        val_expr = resolve_expr(p4_state, self.val)
        return val_expr


def z3_cast(val, to_size):

    if isinstance(val, int):
        # It can happen that we get an int, cast it to a bit vector.
        return z3.BitVecVal(val, to_size)
    val_size = val.size()
    if val_size < to_size:
        return z3.ZeroExt(to_size - val_size, val)
    else:
        slice_l = val_size - 1
        slice_r = val_size - to_size
        return z3.Extract(slice_l, slice_r, val)


class P4Cast(P4Z3Class):
    # TODO: need to take a closer look on how to do this correctly...
    # If we cast do we add/remove the least or most significant bits?
    def __init__(self, val, to_size: z3.BitVecSortRef):
        self.val = val
        self.to_size = to_size.size()

    def eval(self, p4_state):
        expr = resolve_expr(p4_state, self.val)
        expr = check_bool(expr)
        return z3_cast(expr, self.to_size)


class P4Mux(P4Z3Class):
    def __init__(self, condition, then_val, else_val):
        self.condition = condition
        self.then_val = then_val
        self.else_val = else_val

    def eval(self, p4_state):
        condition = resolve_expr(p4_state, self.condition)
        then_val = resolve_expr(p4_state, self.then_val)
        else_val = resolve_expr(p4_state, self.else_val)
        return z3.If(condition, then_val, else_val)


class P4Declaration(P4Z3Class):
    # TODO: Add some more declaration checks here.
    # the difference between a P4Declaration and a P4Assignment is that
    # we resolve the variable in the P4Assignment
    # in the declaration we assign variables as is.
    # they are resolved at runtime by other classes
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_state):
        p4_state.set_or_add_var(self.lval, self.rval)
        return base.step(p4_state)


class P4Initializer(P4Z3Class):
    def __init__(self, val, instance):
        self.val = val
        self.instance = instance

    def eval(self, p4_state):
        instance = resolve_expr(p4_state, self.instance)
        val = resolve_expr(p4_state, self.val)
        if isinstance(val, base.P4ComplexType):
            return val
        if isinstance(instance, base.P4ComplexType):
            if isinstance(val, dict):
                for name, val in val.items():
                    val_expr = resolve_expr(p4_state, val)
                    instance.set_or_add_var(name, val_expr)
            elif isinstance(val, list):
                instance.set_list(val)
            else:
                raise RuntimeError(
                    f"P4StructInitializer members {val} not supported!")
            return instance
        else:
            return val


def slice_assign(lval, rval, slice_l, slice_r) -> z3.SortRef:
    lval_max = lval.size() - 1
    if slice_l == lval_max and slice_r == 0:
        # slice is full lvalue, nothing to do
        return rval
    assemble = []
    if slice_l < lval_max:
        # left slice is smaller than the max, leave that chunk unchanged
        assemble.append(z3.Extract(lval_max, slice_l + 1, lval))
    # fill the rval into the slice
    rval = z3_cast(rval, slice_l + 1 - slice_r)
    assemble.append(rval)
    if slice_r > 0:
        # right slice is larger than zero, leave that chunk unchanged
        assemble.append(z3.Extract(slice_r - 1, 0, lval))
    return z3.Concat(*assemble)


class SliceAssignment(P4Z3Class):
    def __init__(self, lval, rval, slice_l, slice_r):
        self.lval = lval
        self.rval = rval
        self.slice_l = slice_l
        self.slice_r = slice_r

    def eval(self, p4_state):
        lval_expr = resolve_expr(p4_state, self.lval)
        rval_expr = resolve_expr(p4_state, self.rval)
        rval_expr = slice_assign(lval_expr, rval_expr,
                                 self.slice_l, self.slice_r)
        assign = AssignmentStatement(self.lval, rval_expr)
        return assign.eval(p4_state)


class AssignmentStatement(P4Z3Class):
    # AssignmentStatements are essentially just a wrapper class for the
    # set_or_add_var ḿethod of the p4 state.
    # All the important logic is handled there.

    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_state):
        log.debug("Assigning %s to %s ", self.rval, self.lval)
        rval_expr = resolve_expr(p4_state, self.rval)
        # any assignment copies the variable
        # do not pass references, for example when assigning structs
        rval_expr = deepcopy(rval_expr)
        p4_state.set_or_add_var(self.lval, rval_expr)
        return base.step(p4_state)


class MethodCallExpr(P4Z3Class):

    def __init__(self, p4_method, *args):
        self.p4_method = p4_method
        self.args = args

    def set_args(self, args):
        self.args = args

    def eval(self, p4_state):
        p4_method = self.p4_method
        if isinstance(p4_method, str):
            # if we get a reference just try to find the method in the state
            p4_method = p4_state.resolve_reference(p4_method)
        if isinstance(p4_method, P4Callable):
            p4_method.set_param_args(arg_prefix="")
            p4_method.merge_args(p4_state, self.args)
            return p4_method.eval(p4_state)
        elif callable(p4_method):
            return p4_method(p4_state, *self.args)
        raise TypeError(f"Unsupported method type {type(p4_method)}!")


class MethodCallStmt(P4Z3Class):

    def __init__(self, method_expr):
        self.method_expr = method_expr

    def eval(self, p4_state):
        return self.method_expr.eval(p4_state)


class BlockStatement(P4Z3Class):

    def __init__(self):
        self.exprs = []

    def preprend(self, expr):
        self.exprs.insert(0, expr)

    def add(self, expr):
        self.exprs.append(expr)

    def eval(self, p4_state):
        p4_state.insert_exprs(self.exprs)
        return base.step(p4_state)


class P4Noop(P4Z3Class):

    def eval(self, p4_state):
        return base.step(p4_state)


class P4Exit(P4Z3Class):

    def eval(self, p4_state):
        # Exit the chain early
        p4_state.clear_expr_chain()
        return base.step(p4_state)


class P4Return(P4Z3Class):
    def __init__(self, expr=None):
        self.expr = expr

    def eval(self, p4_state):
        # all subsequent operations are void
        p4_state.clear_expr_chain()
        if self.expr is None:
            return base.step(p4_state)
        else:
            return self.expr.eval(p4_state)


class P4Callable(P4Z3Class):
    def __init__(self):
        self.block = BlockStatement()
        self.params = []
        self.args = []

    def set_param_args(self, arg_prefix):
        action_args = []
        for param in self.params:
            arg_name = param[1]
            arg_type = param[2]
            if isinstance(arg_type, z3.SortRef):
                action_args.append(
                    z3.Const(f"{arg_prefix}{arg_name}", arg_type))
            else:
                action_args.append(arg_type)
        self.args = action_args

    def merge_args(self, p4_state, *args):
        if len(*args) > len(self.args):
            raise RuntimeError(
                f"Provided arguments {args} exceeds"
                f"possible number of parameters.")
        for index, runtime_arg in enumerate(*args):
            self.args[index] = runtime_arg

    def add_parameter(self, is_ref=None, arg_name=None, arg_type=None):
        self.params.append((is_ref, arg_name, arg_type))

    def get_parameters(self):
        return self.params


class P4Action(P4Callable):

    def __init__(self):
        super(P4Action, self).__init__()

    def add_stmt(self, block):
        if not isinstance(block, BlockStatement):
            raise RuntimeError(f"Expected a block, got {block}!")
        self.block = block

    def __call__(self, p4_state, *args, **kwargs):
        self.args = args
        return self.eval(p4_state)

    def eval(self, p4_state):
        var_buffer = {}

        # save all the variables that may be overridden
        for param in self.params:
            is_ref = param[0]
            param_name = param[1]
            # previous variables in the environment
            prev_val = p4_state.get_var(param_name)
            if not is_ref:
                # ignore variables that do not exist
                var_buffer[param_name] = prev_val

        # override the symbolic entries if we have concrete
        # arguments from the table
        for index, arg in enumerate(self.args):
            log.debug("Setting %s as %s ", param_name, arg)
            param_name = self.params[index][1]
            p4_state.set_or_add_var(param_name, arg)
        # execute the action expression with the new environment
        expr_chain = p4_state.copy_expr_chain()
        p4_state.set_expr_chain([self.block])
        expr = base.step(p4_state)
        # reset to the previous execution chain
        p4_state.set_expr_chain(expr_chain)

        # restore any variables that may have been overridden
        # TODO: Fix to handle state correctly
        for param in self.params:
            is_ref = param[0]
            param_name = param[1]
            if param_name in var_buffer:
                log.debug("Restoring %s", param_name)
                p4_state.set_or_add_var(param_name, var_buffer[param_name])
            elif not is_ref:
                log.debug("Deleting %s", param_name)
                p4_state.del_var(param_name)

        return base.step(p4_state, expr)


class P4Control(P4Callable):

    def __init__(self):
        super(P4Control, self).__init__()
        self.locals = []
        self.state_initializer = None

    def declare_local(self, local_name, local_var):
        decl = P4Declaration(local_name, local_var)
        self.block.add(decl)

    def add_args(self, params):
        self.params = params

    def add_parameter(self, is_ref=None, arg_name=None, arg_type=None):
        self.params.append((is_ref, arg_name, arg_type))

    def add_instance(self, z3_reg, name, params):
        self.params = params
        self.state_initializer = (z3_reg, name)

    def add_stmt(self, stmt):
        self.block.add(stmt)

    def apply(self, p4_state, *p4_args):
        self.args = p4_args
        return self.eval(p4_state)

    def __call__(self, p4_state=None, *args, **kwargs):
        # for controls, the state is not required
        # controls can only be executed with apply statements
        return self

    def eval(self, p4_state=None):
        # initialize the local context of the function for execution
        z3_reg = self.state_initializer[0]
        name = self.state_initializer[1]
        p4_state_context = z3_reg.init_p4_state(name, self.params)
        if not p4_state:
            # There is no state yet, so use the context of the function
            p4_state = p4_state_context

        var_buffer = {}

        # save all the variables that may be overridden
        for param in self.params:
            is_ref = param[0]
            param_name = param[1]
            # previous variables in the environment
            prev_val = p4_state.get_var(param_name)
            var_buffer[param_name] = prev_val

        # override the symbolic entries if we have concrete
        # arguments from the table
        for index, arg in enumerate(self.args):
            var = p4_state.get_var(arg)
            log.debug("Setting %s as %s ", param_name, arg)
            param_name = self.params[index][1]
            p4_state_context.set_or_add_var(param_name, var)
        # execute the action expression with the new environment

        # save the current execution chain
        expr_chain = p4_state.copy_expr_chain()
        p4_state_context.insert_exprs(self.block)
        expr = base.step(p4_state_context)
        for param in self.params:
            is_ref = param[0]
            param_name = param[1]
            if var_buffer[param_name] is not None:
                log.debug("Restoring %s", param_name)
                p4_state.set_or_add_var(param_name, var_buffer[param_name])
            else:
                log.debug("Deleting %s", param_name)
                p4_state.del_var(param_name)
        # restore the old execution chain
        p4_state.expr_chain = expr_chain
        return base.step(p4_state, expr)


class P4Parser(P4Control):
    pass


class P4Extern(P4Callable):
    # TODO: This is quite brittle, requires concrete examination
    def __init__(self, name, z3_reg):
        super(P4Extern, self).__init__()
        self.name = name
        self.z3_reg = z3_reg

    def add_method(self, name, method):
        setattr(self, name, method)

    def add_parameter(self, is_ref=None, arg_name=None, arg_type=None):
        self.params.append((is_ref, arg_name, arg_type))

    def __call__(self, p4_state=None, *args, **kwargs):
        # for controls, the state is not required
        # controls can only be executed with apply statements
        return self

    def eval(self, p4_state):

        for index, arg in enumerate(self.args):
            is_ref = self.params[index][0]
            param_name = self.params[index][1]

            log.debug("Setting %s as %s ", param_name, arg)
            # Because we do not know what the extern is doing
            # we initiate a new z3 const and just overwrite all reference types
            if is_ref:
                # Externs often have generic types until they are called
                # This call resolves the argument and gets its z3 type
                arg_type = get_type(p4_state, arg)
                extern_mod = z3.Const(f"{self.name}_{param_name}", arg_type)
                instance = self.z3_reg.instance(
                    f"{self.name}_{param_name}", arg_type)
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                if isinstance(instance, base.P4ComplexType):
                    instance.propagate_type(extern_mod)
                # Finally, assign a new value to the pass-by-reference argument
                p4_state.set_or_add_var(arg, instance)

        return base.step(p4_state)


class IfStatement(P4Z3Class):

    def __init__(self):
        self.cond = None
        self.then_block = None
        self.else_block = None

    def add_condition(self, cond):
        self.cond = cond

    def add_then_stmt(self, stmt):
        self.then_block = stmt

    def add_else_stmt(self, stmt):
        self.else_block = stmt

    def eval(self, p4_state):
        if self.cond is None:
            raise RuntimeError("Missing condition!")
        cond = resolve_expr(p4_state, self.cond)
        # conditional branching requires a copy of the state for each branch
        # in some sense this copy acts as a phi function
        then_p4_state = deepcopy(p4_state)
        then_expr = self.then_block.eval(then_p4_state)
        if self.else_block:
            else_p4_state = deepcopy(p4_state)
            else_expr = self.else_block.eval(else_p4_state)
            return z3.If(cond, then_expr, else_expr)
        else:
            return z3_implies(p4_state, cond, then_expr)


class SwitchHit(P4Z3Class):
    def __init__(self, table, cases, default_case):
        self.table = table
        self.default_case = default_case
        self.cases = cases

    def eval_cases(self, p4_state, cases):
        expr = self.default_case.eval(p4_state)
        for case in reversed(cases.values()):
            p4_state = deepcopy(p4_state)
            case_expr = case["case_block"].eval(p4_state)
            expr = z3.If(case["match"], case_expr, expr)
        return expr

    def eval_switch_matches(self, table):
        for case_name, case in self.cases.items():
            match_var = case["match_var"]
            action = table.actions[case_name][0]
            self.cases[case_name]["match"] = (match_var == action)

    def eval(self, p4_state):
        self.eval_switch_matches(self.table)
        switch_hit = self.eval_cases(p4_state, self.cases)
        return switch_hit


class SwitchStatement(P4Z3Class):
    # TODO: Fix fall through for switch statement
    def __init__(self, table_str):
        self.table_str = table_str
        self.default_case = BlockStatement()
        self.cases = OrderedDict()

    def add_case(self, action_str):
        # skip default statements, they are handled separately
        if action_str == "default":
            return
        case = {}
        case["match_var"] = z3.Int(f"{self.table_str}_action")
        case["case_block"] = BlockStatement()
        self.cases[action_str] = case

    def add_stmt_to_case(self, action_str, case_stmt):
        if action_str == "default":
            self.default_case.add(case_stmt)
        else:
            case_block = self.cases[action_str]["case_block"]
            case_block.add(case_stmt)

    def eval(self, p4_state):
        table = p4_state.get_var(self.table_str)
        # instantiate the hit expression
        switch_hit = SwitchHit(table, self.cases, self.default_case)
        p4_state.insert_exprs([table, switch_hit])
        return base.step(p4_state)


class P4Table(P4Z3Class):

    def __init__(self, name):
        self.name = name
        self.keys = []
        self.const_entries = []
        self.actions = OrderedDict()
        self.default_action = None
        self.tbl_action = z3.Int(f"{self.name}_action")

    def add_action(self, action_expr):
        action_name, action_args = resolve_action(action_expr)
        index = len(self.actions) + 1
        self.actions[action_name] = (index, action_name, action_args)

    def add_default(self, action_expr):
        action_name, action_args = resolve_action(action_expr)
        self.default_action = (0, action_name, action_args)

    def add_match(self, table_key):
        self.keys.append(table_key)

    def add_const_entry(self, const_keys, action_expr):

        if len(self.keys) != len(const_keys):
            raise RuntimeError("Constant keys must match table keys!")
        action_name, action_args = resolve_action(action_expr)
        self.const_entries.append((const_keys, (action_name, action_args)))

    def apply(self, p4_state):
        return self.eval(p4_state)

    def __call__(self, p4_state):
        # tables can only be executed with apply statements
        return self

    def eval_keys(self, p4_state):
        key_pairs = []
        if not self.keys:
            # there is nothing to match with...
            return z3.BoolVal(False)
        for index, key in enumerate(self.keys):
            key_eval = resolve_expr(p4_state, key)
            key_sort = get_type(p4_state, key_eval)
            key_match = z3.Const(f"{self.name}_key_{index}", key_sort)
            key_pairs.append(key_eval == key_match)
        return z3.And(key_pairs)

    def eval_action(self, p4_state, action_tuple):
        p4_action = action_tuple[0]
        p4_action_args = action_tuple[1]
        p4_action = p4_state.get_var(p4_action)
        if not isinstance(p4_action, P4Action):
            raise TypeError(f"Expected a P4Action got {type(p4_action)}!")
        # evaluating an action may modify the state of the class
        # so we have to make a copy here for both state and action
        p4_state = deepcopy(p4_state)
        p4_action = deepcopy(p4_action)
        p4_action.set_param_args(arg_prefix=self.name)
        p4_action.merge_args(p4_state, p4_action_args)
        p4_state.insert_exprs(p4_action)
        return base.step(p4_state)

    def eval_default(self, p4_state):
        if self.default_action is None:
            # In case there is no default action, the first action is default
            self.default_action = (0, "NoAction", [])
        _, action_name, p4_action_args = self.default_action
        return self.eval_action(p4_state,
                                (action_name, p4_action_args))

    def eval_table(self, p4_state):
        actions = self.actions
        const_entries = self.const_entries

        # first evaluate the default entry
        expr = self.eval_default(p4_state)
        # then wrap constant entries around it
        for const_keys, action in reversed(const_entries):
            action_name = action[0]
            p4_action_args = action[1]
            matches = []
            # match the constant keys with the normal table keys
            # this generates the match expression for a specific constant entry
            for index, key in enumerate(self.keys):
                key_eval = resolve_expr(p4_state, key)
                const_key = const_keys[index]
                # default implies don't care, do not add
                # TODO: Verify that this assumption is right...
                if str(const_key) == "default":
                    continue
                c_key_eval = resolve_expr(
                    p4_state, const_keys[index])
                matches.append(key_eval == c_key_eval)
            action_match = z3.And(*matches)
            action_tuple = (action_name, p4_action_args)
            action_expr = self.eval_action(p4_state, action_tuple)
            expr = z3.If(action_match, action_expr, expr)
        # then wrap dynamic table entries around the constant entries
        for action in reversed(actions.values()):
            p4_action_id = action[0]
            action_name = action[1]
            p4_action_args = action[2]
            action_match = (self.tbl_action == z3.IntVal(p4_action_id))
            action_tuple = (action_name, p4_action_args)
            action_expr = self.eval_action(p4_state, action_tuple)
            expr = z3.If(action_match, action_expr, expr)
        # finally return a nested set of if expressions
        return expr

    def eval(self, p4_state):
        # This is a table match where we look up the provided key
        # If we match select the associated action,
        # else use the default action
        # TODO: Check the exact semantics how default actions can be called
        # Right now, they can be called in either the table match or miss
        tbl_match = self.eval_keys(p4_state)
        table_expr = self.eval_table(p4_state)
        def_expr = self.eval_default(p4_state)
        return z3.If(tbl_match, table_expr, def_expr)
