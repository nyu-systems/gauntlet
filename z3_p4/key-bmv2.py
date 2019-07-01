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

# the table constant we are matching with
# actually this should be a match action tuple that picks the next action
# how to implement that? Some form of array?
# actually, each table function should emit the header and egress spec as
# they can potentially modify it
MA = Datatype('match_action')
MA.declare('mk_match', ('match', BitVecSort(32)), ('action', IntSort()))
MA = MA.create()


# TODO: Add some notion of egress spec


def control_ingress_0(h, c_match):
    # This is the initial version of the program
    def c_a_0():
        # This action creates a new header type where b is set to a
        return HDR.mk_h(HDR.a(h), HDR.a(h))

    def NoAction_0():
        # NoAction just returns the current header as is
        return h

    def default():
        # The default action
        # It is set to NoAction in this case
        return NoAction_0()

    def c_t():
        def select_action():
            return If(MA.action(c_match) == 1,
                      c_a_0(),
                      (If(MA.action(c_match) == 2,
                          NoAction_0(),
                          default()  # this should be an abort of some form
                          ))
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key = HDR.a(h) + HDR.a(h)
        return If(key == MA.match(c_match),
                  select_action(), default())
    # begin apply
    h_ret = c_t()
    return h_ret


def control_ingress_1(h, c_match):
    # This is the emitted program after pass

    key_0 = BitVec('key_0', 32)

    def c_a_0():
        # This action creates a new header type where b is set to a
        return HDR.mk_h(HDR.a(h), HDR.a(h))

    def NoAction_0():
        # NoAction just returns the current header as is
        return h

    def default():
        # The default action
        # It is set to NoAction in this case
        return NoAction_0()

    def c_t():
        def select_action():
            return If(MA.action(c_match) == 1,
                      c_a_0(),
                      If(MA.action(c_match) == 2,
                         NoAction_0(),
                         default()  # this should be an abort of some form
                         )
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        # Right now, it is ill-defined
        key = key_0
        return If(key == MA.match(c_match),
                  select_action(), default())

    # begin apply
    key_0 = HDR.a(h) + HDR.a(h)
    h_ret = c_t()
    return h_ret


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same

    s = Solver()

    # define the header and match-action entries
    h = Const('h', HDR)
    c_match = Const('match_action', MA)
    # reduce the range of action outputs to the total number of actions
    s.add(0 < MA.action(c_match), MA.action(c_match) < 2)

    # the equivalence equation
    s.add(ForAll([h, c_match],
                 (control_ingress_0(h, c_match) ==
                  control_ingress_1(h, c_match))
                 ))

    print (s.sexpr())
    ret = s.check()
    if ret == sat:
        print (s.model())
    else:
        print (ret)


if __name__ == '__main__':
    z3_check()
