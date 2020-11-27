import operator as op
from p4z3.base import log, z3_cast, z3, copy, handle_mux
from p4z3.base import StructInstance, P4Expression, P4ComplexType
from p4z3.base import merge_attrs, UNDEF_LABEL


class P4Initializer(P4Expression):
    def __init__(self, val, instance_type=None):
        self.val = val
        self.instance_type = instance_type

    def eval(self, ctx):
        val = ctx.resolve_expr(self.val)
        if self.instance_type is None:
            # no type defined, return just the value
            return val
        else:
            instance = ctx.gen_instance(UNDEF_LABEL, self.instance_type)

        if isinstance(val, StructInstance):
            # copy the reference if we initialize with another complex type
            return copy.copy(val)
        if isinstance(instance, StructInstance):
            if isinstance(val, dict):
                instance.setValid()
                for name, val in val.items():
                    val_expr = ctx.resolve_expr(val)
                    instance.set_or_add_var(name, val_expr)
            elif isinstance(val, list):
                instance.set_list(val)
            else:
                raise RuntimeError(
                    f"P4StructInitializer members {val} not supported!")
            return instance
        else:
            # cast the value we assign to the instance we create
            # FIXME: I do not like this, there must be a better way to do this
            if isinstance(val, int) and isinstance(instance, (z3.BitVecSortRef, z3.BitVecRef)):
                val = z3_cast(val, instance.sort())
            return val


class P4Op(P4Expression):
    def get_value(self):
        raise NotImplementedError("get_value")

    def eval(self, ctx):
        raise NotImplementedError("eval")


class P4BinaryOp(P4Op):
    def __init__(self, lval, rval, operator):
        self.lval = lval
        self.rval = rval
        self.operator = operator

    def get_value(self):
        # TODO: This is a kind of hacky function to work around bitvectors
        # There must be a better way to implement this
        # FIXME: Resolve this with state, actually...
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

    def eval(self, ctx):
        lval_expr = ctx.resolve_expr(self.lval)
        rval_expr = ctx.resolve_expr(self.rval)
        # align the bitvectors to allow operations
        lval_is_bitvec = isinstance(lval_expr, (z3.BitVecRef, z3.BitVecNumRef))
        rval_is_bitvec = isinstance(rval_expr, (z3.BitVecRef, z3.BitVecNumRef))
        if lval_is_bitvec and rval_is_bitvec:
            rval_expr = z3_cast(rval_expr, lval_expr.size())
        elif lval_is_bitvec and isinstance(rval_expr, int):
            rval_expr = z3_cast(rval_expr, lval_expr.size())
        elif rval_is_bitvec and isinstance(lval_expr, int):
            lval_expr = z3_cast(lval_expr, rval_expr.size())

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

    def eval(self, ctx):
        expr = ctx.resolve_expr(self.val)
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
        def operator(x, y):
            # for some reason, z3 borks if you use an int as x?
            if isinstance(x, int) and isinstance(y, z3.BitVecRef):
                x = z3_cast(x, y)
            return op.sub(x, y)

        P4BinaryOp.__init__(self, lval, rval, operator)


class P4addsat(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            no_overflow = z3.BVAddNoOverflow(x, y, False)
            no_underflow = z3.BVAddNoUnderflow(x, y)
            max_return = 2**x.size() - 1
            return z3.If(z3.And(no_overflow, no_underflow), x + y, max_return)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4subsat(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            no_overflow = z3.BVSubNoOverflow(x, y)
            no_underflow = z3.BVSubNoUnderflow(x, y, False)
            zero_return = 0
            return z3.If(z3.And(no_overflow, no_underflow), x - y, zero_return)

        P4BinaryOp.__init__(self, lval, rval, operator)


class P4mul(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.mul
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4mod(P4BinaryOp):
    def __init__(self, lval, rval):
        # P4 only supports positive unsigned modulo operations
        def operator(x, y):
            # z3 requires at least one value to be a bitvector for SRem
            # use normal modulo ops instead
            if isinstance(y, int) and isinstance(x, int):
                return op.mod(x, y)
            return z3.URem(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4pow(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.pow
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4band(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # this extra check is necessary because of z3...
            if z3.is_int(x) and isinstance(y, z3.BitVecRef):
                x = z3_cast(x, y)
            if z3.is_int(y) and isinstance(x, z3.BitVecRef):
                y = z3_cast(y, x)
            return op.and_(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4bor(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # this extra check is necessary because of z3...
            if z3.is_int(x) and isinstance(y, z3.BitVecRef):
                x = z3_cast(x, y)
            if z3.is_int(y) and isinstance(x, z3.BitVecRef):
                y = z3_cast(y, x)
            return op.or_(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4land(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = z3.And
        P4BinaryOp.__init__(self, lval, rval, operator)

    def eval(self, ctx):
        # boolean expressions can short-circuit
        # so we save the result of the right-hand expression and merge
        lval_expr = ctx.resolve_expr(self.lval)
        var_store = ctx.checkpoint()
        forward_cond_copy = ctx.tmp_forward_cond
        ctx.tmp_forward_cond = z3.And(forward_cond_copy, lval_expr)
        rval_expr = ctx.resolve_expr(self.rval)
        else_vars = ctx.get_attrs()
        ctx.restore(var_store)
        ctx.tmp_forward_cond = forward_cond_copy
        merge_attrs(ctx, lval_expr, else_vars)
        return self.operator(lval_expr, rval_expr)


class P4lor(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = z3.Or
        P4BinaryOp.__init__(self, lval, rval, operator)

    def eval(self, ctx):
        # boolean expressions can short-circuit
        # so we save the result of the right-hand expression and merge
        lval_expr = ctx.resolve_expr(self.lval)
        var_store = ctx.checkpoint()
        forward_cond_copy = ctx.tmp_forward_cond
        ctx.tmp_forward_cond = z3.And(forward_cond_copy, z3.Not(lval_expr))
        rval_expr = ctx.resolve_expr(self.rval)
        else_vars = ctx.get_attrs()
        ctx.restore(var_store)
        ctx.tmp_forward_cond = forward_cond_copy
        merge_attrs(ctx, z3.Not(lval_expr), else_vars)

        return self.operator(lval_expr, rval_expr)


class P4xor(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = op.xor
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4div(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # z3 requires at least one value to be a bitvector for UDiv
            if isinstance(y, int) and isinstance(x, int):
                return op.floordiv(x, y)
            return z3.UDiv(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lshift(P4BinaryOp):
    def __init__(self, lval, rval):
        P4BinaryOp.__init__(self, lval, rval, None)

    def eval(self, ctx):
        # z3 does not like to shift operators of different size
        # but casting both values could lead to missing an overflow
        # so after the operation cast the lvalue down to its original size
        lval_expr = ctx.resolve_expr(self.lval)
        rval_expr = ctx.resolve_expr(self.rval)
        if isinstance(lval_expr, int):
            # if lval_expr is an int we might get a signed value
            # the only size adjustment is to make the rval expr large enough
            # for some reason a small rval leads to erroneous shifts...
            return op.lshift(lval_expr, rval_expr)
        if isinstance(rval_expr, int):
            # shift is larger than width, all zero
            if lval_expr.size() <= rval_expr:
                return z3.BitVecVal(0, lval_expr.size())
        # align the bitvectors to allow operations
        lval_is_bitvec = isinstance(lval_expr, z3.BitVecRef)
        rval_is_bitvec = isinstance(rval_expr, z3.BitVecRef)
        orig_lval_size = lval_expr.size()
        if lval_is_bitvec and rval_is_bitvec:
            # shift is larger than width, all zero
            if lval_expr.size() <= rval_expr.size():
                lval_expr = z3_cast(lval_expr, rval_expr.size())
            if lval_expr.size() > rval_expr.size():
                rval_expr = z3_cast(rval_expr, lval_expr.size())
        return z3_cast(op.lshift(lval_expr, rval_expr), orig_lval_size)


class P4rshift(P4BinaryOp):
    def __init__(self, lval, rval):
        P4BinaryOp.__init__(self, lval, rval, None)

    def eval(self, ctx):
        # z3 does not like to shift operators of different size
        # but casting both values could lead to missing an overflow
        # so after the operation cast the lvalue down to its original size
        lval_expr = ctx.resolve_expr(self.lval)
        rval_expr = ctx.resolve_expr(self.rval)
        if isinstance(lval_expr, int):
            # if x is an int we might get a signed value
            # we need to use the arithmetic right shift in this case
            return op.rshift(lval_expr, rval_expr)
        # align the bitvectors to allow operations
        lval_is_bitvec = isinstance(lval_expr, z3.BitVecRef)
        rval_is_bitvec = isinstance(rval_expr, z3.BitVecRef)
        orig_lval_size = lval_expr.size()
        if lval_is_bitvec and rval_is_bitvec:
            if lval_expr.size() < rval_expr.size():
                lval_expr = z3_cast(lval_expr, rval_expr.size())
            if lval_expr.size() > rval_expr.size():
                rval_expr = z3_cast(rval_expr, lval_expr.size())
        return z3_cast(z3.LShR(lval_expr, rval_expr), orig_lval_size)


class P4eq(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # this trick ensures that we always return a z3 value
            return op.eq(x, y) == z3.BoolVal(True)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4ne(P4BinaryOp):
    def __init__(self, lval, rval):
        # op.ne does not work quite right, this is the z3 way to do it
        def operator(x, y):
            return z3.Not(op.eq(x, y))
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lt(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # if x and y are ints we might deal with a signed value
            # we need to use the normal operator in this case
            if isinstance(x, int) and isinstance(y, int):
                return op.lt(x, y) == z3.BoolVal(True)
            return z3.ULT(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4le(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # if x and y are ints we might deal with a signed value
            # we need to use the normal operator in this case
            if isinstance(x, int) and isinstance(y, int):
                return op.le(x, y) == z3.BoolVal(True)
            return z3.ULE(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4ge(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # if x and y are ints we might deal with a signed value
            # we need to use the normal operator in this case
            if isinstance(x, int) and isinstance(y, int):
                return op.ge(x, y) == z3.BoolVal(True)
            return z3.UGE(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4gt(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # if x and y are ints we might deal with a signed value
            # we need to use the normal operator in this case
            if isinstance(x, int) and isinstance(y, int):
                return op.gt(x, y) == z3.BoolVal(True)
            return z3.UGT(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4Concat(P4Expression):
    def __init__(self, lval, rval):
        self.lval = lval
        self.rval = rval

    def eval(self, ctx):
        # for concat we do not align the size of the operators
        lval = ctx.resolve_expr(self.lval)
        rval = ctx.resolve_expr(self.rval)
        # all values must be bitvectors... so cast them
        # this is necessary because int<*> values can be concatenated
        if isinstance(lval, int):
            lval = lval.as_bitvec
        if isinstance(rval, int):
            rval = rval.as_bitvec
        return z3.Concat(lval, rval)


class P4Cast(P4BinaryOp):
    # TODO: need to take a closer look on how to do this correctly...
    # FIXME: Clean this up
    # If we cast do we add/remove the least or most significant bits?
    def __init__(self, val, to_size):
        self.val = val
        self.to_size = to_size
        operator = z3_cast
        P4BinaryOp.__init__(self, val, to_size, operator)

    def eval(self, ctx):
        lval_expr = ctx.resolve_expr(self.lval)

        rval_expr = ctx.resolve_type(self.rval)

        # it can happen that we cast to a complex type...
        if isinstance(rval_expr, P4ComplexType):
            # we produce an initializer that takes care of the details
            initializer = P4Initializer(lval_expr, rval_expr)
            return initializer.eval(ctx)
        return self.operator(lval_expr, rval_expr)


class P4Mux(P4Expression):
    def __init__(self, cond, then_val, else_val):
        self.cond = cond
        self.then_val = then_val
        self.else_val = else_val

    def eval(self, ctx):
        cond = z3.simplify(ctx.resolve_expr(self.cond))

        # handle side effects for function and table calls
        if z3.is_true(cond):
            return ctx.resolve_expr(self.then_val)
        if z3.is_false(cond):
            return ctx.resolve_expr(self.else_val)

        var_store = ctx.checkpoint()
        forward_cond_copy = ctx.tmp_forward_cond
        ctx.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        then_expr = ctx.resolve_expr(self.then_val)
        then_vars = ctx.get_attrs()
        ctx.restore(var_store)
        ctx.tmp_forward_cond = forward_cond_copy

        else_expr = ctx.resolve_expr(self.else_val)
        merge_attrs(ctx, cond, then_vars)

        return handle_mux(cond, then_expr, else_expr)
