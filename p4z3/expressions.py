from p4z3.base import log, z3_cast, z3, op
from p4z3.base import P4ComplexType, P4Expression
from p4z3.callables import P4Method


class P4Initializer(P4Expression):
    def __init__(self, val, instance):
        self.val = val
        self.instance = instance

    def eval(self, p4_state):
        instance = p4_state.resolve_expr(self.instance)
        val = p4_state.resolve_expr(self.val)
        if isinstance(val, P4ComplexType):
            return val
        if isinstance(instance, P4ComplexType):
            if isinstance(val, dict):
                for name, val in val.items():
                    val_expr = p4_state.resolve_expr(val)
                    instance.set_or_add_var(name, val_expr)
            elif isinstance(val, list):
                instance.set_list(val)
            else:
                log.info(type(val))
                log.info(instance)
                log.info(type(instance))
                raise RuntimeError(
                    f"P4StructInitializer members {val} not supported!")
            return instance
        else:
            # cast the value we assign to the instance we create
            # TODO: I do not like this, there must be a better way to do this
            if isinstance(val, int):
                val = z3_cast(val, instance.sort())
            return val


class MethodCallExpr(P4Expression):

    def __init__(self, p4_method, type_args, *args, **kwargs):
        self.p4_method = p4_method
        self.args = args
        self.kwargs = kwargs
        self.type_args = type_args

    def eval(self, p4_state):
        p4_method = self.p4_method
        # if we get a reference just try to find the method in the state
        if not callable(p4_method):
            p4_method = p4_state.resolve_expr(p4_method)
        # TODO: Figure out how these type bindings work
        # if isinstance(p4_method, P4Method):
            # p4_method.initialize(*self.type_args)
        if callable(p4_method):
            return p4_method(p4_state, *self.args, **self.kwargs)
        raise TypeError(f"Unsupported method type {type(p4_method)}!")


class P4Op(P4Expression):
    def get_value(self):
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
        lval_expr = p4_state.resolve_expr(self.lval)
        rval_expr = p4_state.resolve_expr(self.rval)
        # align the bitvectors to allow operations
        lval_is_bitvec = isinstance(lval_expr, z3.BitVecRef)
        rval_is_bitvec = isinstance(rval_expr, z3.BitVecRef)
        if lval_is_bitvec and rval_is_bitvec:
            if lval_expr.size() < rval_expr.size():
                lval_expr = z3_cast(lval_expr, rval_expr.size())
            if lval_expr.size() > rval_expr.size():
                rval_expr = z3_cast(rval_expr, lval_expr.size())
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
        expr = p4_state.resolve_expr(self.val)
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
    def __init__(self, lval, rval):
        def operator(x, y):
            no_overflow = z3.BVAddNoOverflow(x, y, False)
            no_underflow = z3.BVAddNoUnderflow(x, y)
            max_return = z3.BitVecVal((2**x.size()) - 1, x.sort())
            return z3.If(z3.And(no_overflow, no_underflow), x + y, max_return)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4subsat(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            no_overflow = z3.BVSubNoOverflow(x, y)
            no_underflow = z3.BVSubNoUnderflow(x, y, False)
            zero_return = z3.BitVecVal(0, x.sort())
            return z3.If(z3.And(no_overflow, no_underflow), x - y, zero_return)

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
        def operator(x, y):
            # z3 requires at least one value to be a bitvector for UDiv
            if isinstance(y, int) and isinstance(x, int):
                x = x.as_bitvec
                y = y.as_bitvec
            return z3.UDiv(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lshift(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.lshift
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4rshift(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # if x is an int we might get a signed value
            # we need to use the arithmetic right shift in this case
            if isinstance(x, int):
                return op.rshift(x, y)
            return z3.LShR(x, y)
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
        # op.ne does not work quite right, this is the z3 way to do it
        def operator(x, y):
            return z3.Not(op.eq(x, y))
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


class P4Concat(P4Expression):
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, p4_state):
        # for concat we do not align the size of the operators
        lval = p4_state.resolve_expr(self.lval)
        rval = p4_state.resolve_expr(self.rval)
        # all values must be bitvectors... so cast them
        if isinstance(lval, int):
            lval = lval.as_bitvec
        if isinstance(rval, int):
            rval = rval.as_bitvec
        return z3.Concat(lval, rval)


class P4Cast(P4BinaryOp):
    # TODO: need to take a closer look on how to do this correctly...
    # If we cast do we add/remove the least or most significant bits?
    def __init__(self, val, to_size):
        self.val = val
        self.to_size = to_size
        operator = z3_cast
        P4BinaryOp.__init__(self, val, to_size, operator)


class P4Mux(P4Expression):
    def __init__(self, cond, then_val, else_val):
        self.cond = cond
        self.then_val = then_val
        self.else_val = else_val

    def unravel_datatype(self, complex_type, datatype_list):
        unravelled_list = []
        for val in datatype_list:
            if isinstance(complex_type, P4ComplexType):
                val = complex_type.resolve_reference(val)
            if isinstance(val, P4ComplexType):
                val_list = list(val.members)
                val = self.unravel_datatype(val, val_list)
            unravelled_list.append(val)
        return unravelled_list

    def eval(self, p4_state):
        cond = p4_state.resolve_expr(self.cond)
        then_val = p4_state.resolve_expr(self.then_val)
        else_val = p4_state.resolve_expr(self.else_val)
        then_expr = then_val
        else_expr = else_val
        # this is a really nasty hack, do not try this at home kids
        # because we have to be able to access the sub values again
        # we have to resolve the if condition in the case of complex types
        # we do this by splitting the if statement into a list
        # lists can easily be assigned to a target structure
        if isinstance(then_expr, P4ComplexType):
            then_expr = list(then_expr.members)
        if isinstance(else_expr, P4ComplexType):
            else_expr = list(else_expr.members)
        if isinstance(then_expr, list) and isinstance(else_expr, list):
            sub_cond = []
            # handle nested complex types
            then_expr = self.unravel_datatype(then_val, then_expr)
            else_expr = self.unravel_datatype(else_val, else_expr)
            for idx, member in enumerate(then_expr):
                if_expr = z3.If(cond, member, else_expr[idx])
                sub_cond.append(if_expr)
            return sub_cond
        return z3.If(cond, then_expr, else_expr)
