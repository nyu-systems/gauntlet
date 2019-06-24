# (declare-const key (_ BitVec 32))
# (declare-datatypes () ((H (mk-h (a (_ BitVec 32)) (b (_ BitVec 32)) ))))
# (declare-const h H)
# (define-fun pass_0 ((h H)) (H)
#     (ite (= (bvadd (a h) (a h)) key) (mk-h (a h) (a h)) (mk-h (a h) (b h)) )
# )
# (define-const key_0 (_ BitVec 32) (bvadd (a h) (a h)))
# (define-fun pass_1 ((h H)) (H)
#     (ite (= key_0 key)  (mk-h (a h) (a h)) (mk-h (a h) (b h)) )
# )
# (assert (not ( = (pass_0 h) (pass_1 h))))
# (check-sat)


from z3 import *

# declaration of the global header type that is to be parsed
HDR = Datatype('hdr')
HDR.declare('mk_h', ('a', BitVecSort(32)), ('b', BitVecSort(32)))
HDR = HDR.create()
h = Const('h', HDR)

# the table constant we are matching with
# actually this should be a match action tuple that picks the next action
# how to implement that?
# actually, each table function should emit the header and egress spec as they
# can potentially modify it
table_c_match = BitVec('table_c_match', 32)

# TODO: Add some notion of egress spec


def c_a_0():
    # This action create a new header type where b is set to a
    return HDR.mk_h(HDR.a(h), HDR.a(h))

# NoAction just emits the packet


def NoAction_0():
    # NoAction just returns the current header as is
    return h


def default():
    # The default action
    # It is set to NoAction in this case
    return NoAction_0()


def c_t(key):
    # This is a table match where we look up the provided key
    # Key probably has to be a datatype, too
    return If(key == table_c_match,
              c_a_0(), default())


def control_ingress_0():
    # This is the initial version of the program
    return c_t(HDR.a(h) + HDR.a(h))


def control_ingress_1():
    # This is the emitted program after pass
    key_0 = HDR.a(h) + HDR.a(h)
    return c_t(key_0)


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should be
    # the same
    s = Solver()
    s.add(ForAll([h, table_c_match],
                 (control_ingress_0() == control_ingress_1())))
    print (s.sexpr())
    print (s.check())
    try:
        print (s.model())
    except Z3Exception as e:
        print("Error while trying to emit model: %s" % e)


if __name__ == '__main__':
    z3_check()
