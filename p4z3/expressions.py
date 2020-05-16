import operator as op
from p4z3.base import log, z3_cast, z3, copy_attrs, copy, gen_instance
from p4z3.base import P4ComplexInstance, P4Expression, P4ComplexType


class P4Initializer(P4Expression):
    def __init__(self, val, instance_type=None):
        self.val = val
        self.instance_type = instance_type

    def eval(self, p4_state):
        val = p4_state.resolve_expr(self.val)
        if self.instance_type is None:
            # no type defined, return just the value
            return val
        else:
            instance = gen_instance("None", self.instance_type)

        if isinstance(val, P4ComplexInstance):
            # copy the reference if we initialize with another complex type
            return copy.copy(val)
        if isinstance(instance, P4ComplexInstance):
            if isinstance(val, dict):
                instance.setValid()
                for name, val in val.items():
                    val_expr = p4_state.resolve_expr(val)
                    instance.set_or_add_var(name, val_expr)
            elif isinstance(val, list):
                instance.set_list(val)
            else:
                raise RuntimeError(
                    f"P4StructInitializer members {val} not supported!")
            return instance
        else:
            # cast the value we assign to the instance we create
            # TODO: I do not like this, there must be a better way to do this
            if isinstance(val, int) and isinstance(instance, (z3.BitVecSortRef, z3.BitVecRef)):
                val = z3_cast(val, instance.sort())
            return val


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
        lval_is_bitvec = isinstance(lval_expr, (z3.BitVecRef, z3.BitVecNumRef))
        rval_is_bitvec = isinstance(rval_expr, (z3.BitVecRef, z3.BitVecNumRef))
        if lval_is_bitvec and rval_is_bitvec:
            if lval_expr.size() < rval_expr.size():
                rval_expr = z3_cast(rval_expr, lval_expr.size())
            if lval_expr.size() > rval_expr.size():
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

    def eval(self, p4_state):
        # boolean expressions can short-circuit
        # so we save the result of the right-hand expression and merge
        lval_expr = p4_state.resolve_expr(self.lval)
        var_store, chain_copy = p4_state.checkpoint()
        rval_expr = p4_state.resolve_expr(self.rval)
        else_vars = copy_attrs(p4_state.locals)
        p4_state.restore(var_store, chain_copy)
        p4_state.merge_attrs(lval_expr, else_vars)
        return self.operator(lval_expr, rval_expr)


class P4lor(P4BinaryOp):
    def __init__(self, lval, rval):
        operator = z3.Or
        P4BinaryOp.__init__(self, lval, rval, operator)

    def eval(self, p4_state):
        # boolean expressions can short-circuit
        # so we save the result of the right-hand expression and merge
        lval_expr = p4_state.resolve_expr(self.lval)
        var_store, chain_copy = p4_state.checkpoint()
        rval_expr = p4_state.resolve_expr(self.rval)
        else_vars = copy_attrs(p4_state.locals)
        p4_state.restore(var_store, chain_copy)
        p4_state.merge_attrs(z3.Not(lval_expr), else_vars)

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
                x = x.as_bitvec
                y = y.as_bitvec
                return op.truediv(x, y)
            return z3.UDiv(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4lshift(P4BinaryOp):
    def __init__(self, lval, rval):
        P4BinaryOp.__init__(self, lval, rval, None)

    def eval(self, p4_state):
        # z3 does not like to shift operators of different size
        # but casting both values could lead to missing an overflow
        # so after the operation cast the lvalue down to its original size
        lval_expr = p4_state.resolve_expr(self.lval)
        rval_expr = p4_state.resolve_expr(self.rval)
        if isinstance(lval_expr, int):
            # if lval_expr is an int we might get a signed value
            # the only size adjustment is to make the rval expr large enough
            # for some reason a small rval leads to erroneous shifts...
            return op.lshift(lval_expr, z3_cast(rval_expr, 32))
        # align the bitvectors to allow operations
        lval_is_bitvec = isinstance(lval_expr, z3.BitVecRef)
        rval_is_bitvec = isinstance(rval_expr, z3.BitVecRef)
        orig_lval_size = lval_expr.size()
        if lval_is_bitvec and rval_is_bitvec:
            if lval_expr.size() < rval_expr.size():
                lval_expr = z3_cast(lval_expr, rval_expr.size())
            if lval_expr.size() > rval_expr.size():
                rval_expr = z3_cast(rval_expr, lval_expr.size())
        return z3_cast(op.lshift(lval_expr, rval_expr), orig_lval_size)


class P4rshift(P4BinaryOp):
    def __init__(self, lval, rval):
        P4BinaryOp.__init__(self, lval, rval, None)

    def eval(self, p4_state):
        # z3 does not like to shift operators of different size
        # but casting both values could lead to missing an overflow
        # so after the operation cast the lvalue down to its original size
        lval_expr = p4_state.resolve_expr(self.lval)
        rval_expr = p4_state.resolve_expr(self.rval)
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
        operator = op.eq
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
                return op.lt(x, y)
            return z3.ULT(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4le(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # if x and y are ints we might deal with a signed value
            # we need to use the normal operator in this case
            if isinstance(x, int) and isinstance(y, int):
                return op.le(x, y)
            return z3.ULE(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4ge(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # if x and y are ints we might deal with a signed value
            # we need to use the normal operator in this case
            if isinstance(x, int) and isinstance(y, int):
                return op.ge(x, y)
            return z3.UGE(x, y)
        P4BinaryOp.__init__(self, lval, rval, operator)


class P4gt(P4BinaryOp):
    def __init__(self, lval, rval):
        def operator(x, y):
            # if x and y are ints we might deal with a signed value
            # we need to use the normal operator in this case
            if isinstance(x, int) and isinstance(y, int):
                return op.gt(x, y)
            # FIXME: Find a better way to model negative comparions
            # right now we have this hack
            if isinstance(x, int) and x < 0:
                return z3.BoolVal(False)
            if isinstance(y, int) and y < 0:
                return z3.BoolVal(True)
            return z3.UGT(x, y)
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
        # this is necessary because int<*> values can be concatenated
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

    def eval(self, p4_state):
        lval_expr = p4_state.resolve_expr(self.lval)
        # it can happen that we cast to a complex type...
        if isinstance(self.rval, P4ComplexType):
            instance = self.rval.instantiate(self.rval.name)
            initializer = P4Initializer(lval_expr, instance)
            return initializer.eval(p4_state)
        rval_expr = p4_state.resolve_expr(self.rval)
        # align the bitvectors to allow operations
        lval_is_bitvec = isinstance(lval_expr, z3.BitVecRef)
        rval_is_bitvec = isinstance(rval_expr, z3.BitVecRef)
        if lval_is_bitvec and rval_is_bitvec:
            if lval_expr.size() < rval_expr.size():
                rval_expr = z3_cast(rval_expr, lval_expr.size())
            if lval_expr.size() > rval_expr.size():
                lval_expr = z3_cast(lval_expr, rval_expr.size())
        return self.operator(lval_expr, rval_expr)


class P4Mux(P4Expression):
    def __init__(self, cond, then_val, else_val):
        self.cond = cond
        self.then_val = then_val
        self.else_val = else_val

    def unravel_datatype(self, complex_type, datatype_list):
        unravelled_list = []
        for val in datatype_list:
            if isinstance(complex_type, P4ComplexInstance):
                val = complex_type.resolve_reference(val)
            if isinstance(val, P4ComplexInstance):
                val_list = list(val.members)
                val = self.unravel_datatype(val, val_list)
            elif isinstance(val, list):
                unravelled_list.extend(val)
            else:
                unravelled_list.append(val)
        return unravelled_list

    def eval(self, p4_state):
        cond = p4_state.resolve_expr(self.cond)
        # handle side effects for function calls
        var_store, chain_copy = p4_state.checkpoint()
        then_val = p4_state.resolve_expr(self.then_val)
        then_vars = copy_attrs(p4_state.locals)
        p4_state.restore(var_store, chain_copy)
        else_val = p4_state.resolve_expr(self.else_val)
        p4_state.merge_attrs(cond, then_vars)

        then_expr = then_val
        else_expr = else_val
        # this is a really nasty hack, do not try this at home kids
        # because we have to be able to access the sub values again
        # we have to resolve the if condition in the case of complex types
        # we do this by splitting the if statement into a list
        # lists can easily be assigned to a target structure
        if isinstance(then_expr, P4ComplexInstance):
            then_expr = then_expr.flatten()
        if isinstance(else_expr, P4ComplexInstance):
            else_expr = else_expr.flatten()
        if isinstance(then_expr, list) and isinstance(else_expr, list):
            sub_cond = []
            # handle nested complex types
            then_expr = self.unravel_datatype(then_val, then_expr)
            else_expr = self.unravel_datatype(else_val, else_expr)
            for idx, member in enumerate(then_expr):
                if_expr = z3.If(cond, member, else_expr[idx])
                sub_cond.append(if_expr)
            return sub_cond
        then_is_const = isinstance(then_expr, (z3.BitVecRef, int))
        else_is_const = isinstance(else_expr, (z3.BitVecRef, int))
        if then_is_const and else_is_const:
            # align the bitvectors to allow operations, we cast ints downwards
            if else_expr.size() > then_expr.size():
                else_expr = z3_cast(else_expr, then_expr.size())
            if else_expr.size() < then_expr.size():
                then_expr = z3_cast(then_expr, else_expr.size())
        return z3.If(cond, then_expr, else_expr)
