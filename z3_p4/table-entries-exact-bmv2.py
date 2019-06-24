from z3 import *

# declaration of the global header type that is to be parsed
HDR = Datatype('hdr')
HDR.declare('mk_hdr',
            ('e', BitVecSort(8)), ('t', BitVecSort(16)),
            ('l', BitVecSort(8)), ('r', BitVecSort(8)),
            ('v', BitVecSort(8)))
HDR = HDR.create()
h = Const('h', HDR)

# the table constant we are matching with
table_match = BitVec('table_match', 32)

# TODO: Add some notion of egress spec


def a_with_control_params(x):
    # This action create a new header type where b is set to a
    return h

# NoAction just emits the packet


def a():
    # NoAction just returns the current header as is
    return h


def default():
    # The default action
    # It is set to NoAction in this case
    return a()


def c_t(key):
    match_0 = BitVecVal(1, 9)
    match_1 = BitVecVal(2, 9)
    # This is a table match where we look up the provided key
    # Key probably has to be a datatype, too
    return If(key == match_0,
              a_with_control_params(match_0), default())


def control_ingress_0():
    # This is the initial version of the program
    return c_t(HDR.e(h))


def control_ingress_1():
    # This is the emitted program after pass
    return c_t(HDR.e(h))


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should be
    # the same
    s = Solver()
    s.add(ForAll([h, table_match],
                 (control_ingress_0() != control_ingress_1())))
    print (s.sexpr())
    print (s.check())
    try:
        print (s.model())
    except Z3Exception as e:
        print("Error while trying to emit model: %s" % e)


if __name__ == '__main__':
    z3_check()
