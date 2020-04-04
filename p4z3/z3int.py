import z3

class Z3Int(int):

    def __new__(cls, val, bit_size=64):
        cls.val = val
        cls.bit_size = bit_size
        cls.as_bitvec = z3.BitVecVal(val, 64)
        return int.__new__(cls, val)

    @staticmethod
    def sort():
        return z3.BitVecSort(Z3Int.bit_size)

    @staticmethod
    def size():
        return Z3Int.bit_size

    def __abs__(self):
        res = super(Z3Int, self).__abs__()
        return self.__class__(res)

    def __add__(self, other):
        res = super(Z3Int, self).__add__(other)
        if res == NotImplemented:
            return other.__add__(self)
        return self.__class__(res)

    def __and__(self, other):
        res = super(Z3Int, self).__and__(other)
        if res == NotImplemented:
            return other.__and__(self)
        return self.__class__(res)

    def __floordiv__(self, other):
        res = super(Z3Int, self).__floordiv__(other)
        if res == NotImplemented:
            return other.__floordiv__(self)
        return self.__class__(res)

    def __invert__(self):
        res = super(Z3Int, self).__invert__()
        return self.__class__(res)

    def __or__(self, other):
        res = super(Z3Int, self).__or__(other)
        if res == NotImplemented:
            return other.__or__(self)
        return self.__class__(res)

    def __lshift__(self, other):
        res = super(Z3Int, self).__lshift__(other)
        if res == NotImplemented:
            return other.__lshift__(self)
        return self.__class__(res)

    def __mod__(self, other):
        res = super(Z3Int, self).__mod__(other)
        if res == NotImplemented:
            return other.__mod__(self)
        return self.__class__(res)

    def __mul__(self, other):
        res = super(Z3Int, self).__mul__(other)
        if res == NotImplemented:
            return other.__mul__(self)
        return self.__class__(res)

    def __pos__(self):
        res = super(Z3Int, self).__pos__()
        return self.__class__(res)

    def __pow__(self, other):
        res = super(Z3Int, self).__pow__(other)
        if res == NotImplemented:
            return other.__pow__(self)
        return self.__class__(res)

    def __rshift__(self, other):
        res = super(Z3Int, self).__rshift__(other)
        if res == NotImplemented:
            return other.__rshift__(self)
        return self.__class__(res)

    def __sub__(self, other):
        res = super(Z3Int, self).__sub__(other)
        if res == NotImplemented:
            return other.__sub__(self)
        return self.__class__(res)

    def __truediv__(self, other):
        res = super(Z3Int, self).__truediv__(other)
        if res == NotImplemented:
            return other.__truediv__(self)
        return self.__class__(res)

    def __xor__(self, other):
        res = super(Z3Int, self).__xor__(other)
        if res == NotImplemented:
            return other.__xor__(self)
        return self.__class__(res)

    def __radd__(self, other):
        res = super(Z3Int, self).__radd__(other)
        if res == NotImplemented:
            return other.__radd__(self)
        return self.__class__(res)

    def __rand__(self, other):
        res = super(Z3Int, self).__rand__(other)
        if res == NotImplemented:
            return other.__rand__(self)
        return self.__class__(res)

    def __rfloordiv__(self, other):
        res = super(Z3Int, self).__rfloordiv__(other)
        if res == NotImplemented:
            return other.__rfloordiv__(self)
        return self.__class__(res)

    def __ror__(self, other):
        res = super(Z3Int, self).__ror__(other)
        if res == NotImplemented:
            return other.__ror__(self)
        return self.__class__(res)

    def __rlshift__(self, other):
        res = super(Z3Int, self).__rlshift__(other)
        if res == NotImplemented:
            return other.__rlshift__(self)
        return self.__class__(res)

    def __rmod__(self, other):
        res = super(Z3Int, self).__rmod__(other)
        if res == NotImplemented:
            return other.__rmod__(self)
        return self.__class__(res)

    def __rmul__(self, other):
        res = super(Z3Int, self).__rmul__(other)
        if res == NotImplemented:
            return other.__rmul__(self)
        return self.__class__(res)

    def __rpow__(self, other):
        res = super(Z3Int, self).__rpow__(other)
        if res == NotImplemented:
            return other.__rpow__(self)
        return self.__class__(res)

    def __rrshift__(self, other):
        res = super(Z3Int, self).__rrshift__(other)
        if res == NotImplemented:
            return other.__rrshift__(self)
        return self.__class__(res)

    def __rsub__(self, other):
        res = super(Z3Int, self).__rsub__(other)
        if res == NotImplemented:
            return other.__rsub__(self)
        return self.__class__(res)

    def __rtruediv__(self, other):
        res = super(Z3Int, self).__rtruediv__(other)
        if res == NotImplemented:
            return other.__rtruediv__(self)
        return self.__class__(res)

    def __rxor__(self, other):
        res = super(Z3Int, self).__rxor__(other)
        if res == NotImplemented:
            return other.__rxor__(self)
        return self.__class__(res)
