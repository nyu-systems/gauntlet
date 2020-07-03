import z3


class Z3Int(int):

    def __new__(cls, val, bit_size=64):
        cls.val = val
        cls.bit_size = bit_size
        cls.as_bitvec = z3.BitVecVal(val, bit_size)
        return int.__new__(cls, val)

    @staticmethod
    def sort():
        return z3.BitVecSort(Z3Int.bit_size)

    @staticmethod
    def size():
        return Z3Int.bit_size

    def __abs__(self):
        res = int.__abs__()
        return Z3Int(res, self.bit_size)

    def __neg__(self):
        res = int.__neg__(self)
        return Z3Int(res, self.bit_size)

    def __add__(self, other):
        res = int.__add__(self, other)
        if res == NotImplemented:
            return other.__add__(self)
        return Z3Int(res, self.bit_size)

    def __and__(self, other):
        res = int.__and__(self, other)
        if res == NotImplemented:
            return other.__and__(self)
        return Z3Int(res, self.bit_size)

    def __floordiv__(self, other):
        res = int.__floordiv__(self, other)
        if res == NotImplemented:
            return other.__floordiv__(self)
        return Z3Int(res, self.bit_size)

    def __invert__(self):
        res = int.__invert__(self)
        return Z3Int(res, self.bit_size)

    def __or__(self, other):
        res = int.__or__(self, other)
        if res == NotImplemented:
            return other.__or__(self)
        return Z3Int(res, self.bit_size)

    def __lshift__(self, other):
        res = int.__lshift__(self, other)
        if res == NotImplemented:
            return other.__lshift__(self)
        return Z3Int(res, self.bit_size)

    def __mod__(self, other):
        res = int.__mod__(self, other)
        if res == NotImplemented:
            return other.__mod__(self)
        return Z3Int(res, self.bit_size)

    def __mul__(self, other):
        res = int.__mul__(self, other)
        if res == NotImplemented:
            return other.__mul__(self)
        return Z3Int(res, self.bit_size)

    def __pos__(self):
        res = int.__pos__()
        return Z3Int(res, self.bit_size)

    def __pow__(self, other):
        res = int.__pow__(self, other)
        if res == NotImplemented:
            return other.__pow__(self)
        return Z3Int(res, self.bit_size)

    def __rshift__(self, other):
        res = int.__rshift__(self, other)
        if res == NotImplemented:
            return other.__rshift__(self)
        return Z3Int(res, self.bit_size)

    def __sub__(self, other):
        res = int.__sub__(self, other)
        if res == NotImplemented:
            return other.__sub__(self)
        return Z3Int(res, self.bit_size)

    def __truediv__(self, other):
        res = int.__truediv__(self, other)
        if res == NotImplemented:
            return other.__truediv__(self)
        return Z3Int(res, self.bit_size)

    def __xor__(self, other):
        res = int.__xor__(self, other)
        if res == NotImplemented:
            return other.__xor__(self)
        return Z3Int(res, self.bit_size)

    def __radd__(self, other):
        res = int.__radd__(self, other)
        if res == NotImplemented:
            return other.__radd__(self)
        return Z3Int(res, self.bit_size)

    def __rand__(self, other):
        res = int.__rand__(self, other)
        if res == NotImplemented:
            return other.__rand__(self)
        return Z3Int(res, self.bit_size)

    def __rfloordiv__(self, other):
        res = int.__rfloordiv__(self, other)
        if res == NotImplemented:
            return other.__rfloordiv__(self)
        return Z3Int(res, self.bit_size)

    def __ror__(self, other):
        res = int.__ror__(self, other)
        if res == NotImplemented:
            return other.__ror__(self)
        return Z3Int(res, self.bit_size)

    def __rlshift__(self, other):
        res = int.__rlshift__(self, other)
        if res == NotImplemented:
            return other.__rlshift__(self)
        return Z3Int(res, self.bit_size)

    def __rmod__(self, other):
        res = int.__rmod__(self, other)
        if res == NotImplemented:
            return other.__rmod__(self)
        return Z3Int(res, self.bit_size)

    def __rmul__(self, other):
        res = int.__rmul__(self, other)
        if res == NotImplemented:
            return other.__rmul__(self)
        return Z3Int(res, self.bit_size)

    def __rpow__(self, other):
        res = int.__rpow__(self, other)
        if res == NotImplemented:
            return other.__rpow__(self)
        return Z3Int(res, self.bit_size)

    def __rrshift__(self, other):
        res = int.__rrshift__(self, other)
        if res == NotImplemented:
            return other.__rrshift__(self)
        return Z3Int(res, self.bit_size)

    def __rsub__(self, other):
        res = int.__rsub__(self, other)
        if res == NotImplemented:
            return other.__rsub__(self)
        return Z3Int(res, self.bit_size)

    def __rtruediv__(self, other):
        res = int.__rtruediv__(self, other)
        if res == NotImplemented:
            return other.__rtruediv__(self)
        return Z3Int(res, self.bit_size)

    def __rxor__(self, other):
        res = int.__rxor__(self, other)
        if res == NotImplemented:
            return other.__rxor__(self)
        return Z3Int(res, self.bit_size)

    # def __lt__(self, other):
    #     res = int.__lt__(self, other)
    #     if res == NotImplemented:
    #         return other.__lt__(self)
    #     return res

    # def __le__(self, other):
    #     res = int.__le__(self, other)
    #     if res == NotImplemented:
    #         return other.__le__(self)
    #     return res

    # def __eq__(self, other):
    #     res = int.__eq__(self, other)
    #     if res == NotImplemented:
    #         return other.__eq__(self)
    #     return res

    # def __ne__(self, other):
    #     res = int.__ne__(self, other)
    #     if res == NotImplemented:
    #         return other.__ne__(self)
    #     return res

    # def __ge__(self, other):
    #     res = int.__ge__(self, other)
    #     if res == NotImplemented:
    #         return other.__ge__(self)
    #     return res

    # def __gt__(self, other):
    #     res = int.__gt__(self, other)
    #     if res == NotImplemented:
    #         return other.__gt__(self)
    #     return res
