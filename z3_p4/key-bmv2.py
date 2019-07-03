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
hdr = Datatype('hdr')
hdr.declare('mk_hdr', ('a', BitVecSort(32)), ('b', BitVecSort(32)))
hdr = hdr.create()

# the final output in a single datatype
p4_output = Datatype('p4_output')
p4_output.declare('mk_output',
                  ('hdr', hdr),
                  ('egress_spec', BitVecSort(9)))
p4_output = p4_output.create()


# the table constant we are matching with
# actually this should be a match action tuple that picks the next action
# how to implement that? Some form of array?
# actually, each table function should emit the header and egress spec as
# they can potentially modify it
ma_c_t = Datatype('ma_c_t')
ma_c_t.declare('mk_ma_c_t', ('key_0', BitVecSort(32)), ('action', IntSort()))
ma_c_t = ma_c_t.create()


# define the header and match-action entries
h = Const('h', hdr)
c_t_m = Const('c_t_m', ma_c_t)


def control_ingress_0(s):
    # This is the initial version of the program
    ret = Const('ret', p4_output)

    # the assignments that happen during the execution of the pipeline
    constraints = []

    def c_a_0():
        # This action creates a new header type where b is set to a
        return (hdr.b(p4_output.hdr(ret)) == hdr.a(h))

    def NoAction_0():
        # NoAction just returns the current header as is
        return Var(True, BoolSort())

    def c_t():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_c_t.action(c_t_m), ma_c_t.action(c_t_m) < 2)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_0()

        def select_action():
            return And(Implies(ma_c_t.action(c_t_m) == 1,
                               c_a_0()),
                       Implies(ma_c_t.action(c_t_m) == 2,
                               NoAction_0()),
                       )
        # This is a table match where we look up the provided key
        key_0 = hdr.a(h) + hdr.a(h)
        return If(key_0 == ma_c_t.key_0(c_t_m),
                  select_action(), default())
    # begin apply
    constraints.append(c_t())
    constraints.append(p4_output.egress_spec(ret) == BitVecVal(0, 9))
    return And(constraints)


def control_ingress_1(s):
    # This is the emitted program after pass
    ret = Const('ret', p4_output)
    # the assignments that happen during the execution of the pipeline
    constraints = []

    key_0 = BitVec('key_0', 32)

    def c_a_0():
        # This action creates a new header type where b is set to a
        return (hdr.b(p4_output.hdr(ret)) == hdr.a(h))

    def NoAction_0():
        # NoAction just returns the current header as is
        return Var(True, BoolSort())

    def c_t():

        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_c_t.action(c_t_m), ma_c_t.action(c_t_m) < 2)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_0()

        def select_action():
            return And(Implies(ma_c_t.action(c_t_m) == 1,
                               c_a_0()),
                       Implies(ma_c_t.action(c_t_m) == 2,
                               NoAction_0()),
                       )
        # This is a table match where we look up the provided key
        nonlocal key_0
        c_t_key_0 = key_0
        return If(c_t_key_0 == ma_c_t.key_0(c_t_m),
                  select_action(), default())

    # begin apply
    key_0 = hdr.a(h) + hdr.a(h)
    constraints.append(c_t())
    constraints.append(p4_output.egress_spec(ret) == BitVecVal(0, 9))
    return And(constraints)


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same

    s = Solver()
    bounds = [h, c_t_m]
    # the equivalence equation
    tv_equiv = ForAll(bounds, (
        eq(simplify(control_ingress_0(s)), simplify(control_ingress_1(s)))))
    s.add(tv_equiv)

    print (s.sexpr())
    ret = s.check()
    if ret == sat:
        print (ret)
        print (s.model())
    else:
        print (ret)


if __name__ == '__main__':
    z3_check()
