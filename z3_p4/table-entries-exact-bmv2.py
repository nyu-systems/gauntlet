from z3 import *

# declaration of the global header type that is to be parsed
HDR = Datatype('hdr')
HDR.declare('mk_hdr',
            ('e', BitVecSort(8)), ('t', BitVecSort(16)),
            ('l', BitVecSort(8)), ('r', BitVecSort(8)),
            ('v', BitVecSort(8)))
HDR = HDR.create()

MA = Datatype('match_action')
MA.declare('mk_match', ('match', BitVecSort(8)), ('action', IntSort()))
MA = MA.create()

# TODO: Add some notion of egress spec


def a_with_control_params(x):
    # This action create a new header type where b is set to a
    return h

# NoAction just emits the packet


def control_ingress_0(h, c_match):
    # This is the emitted program after pass
    egress_spec = BitVecVal(0, 9)

    def a():
        nonlocal egress_spec
        egress_spec = BitVecVal(0, 9)
        return h

    def a_with_control_params(x):
        nonlocal egress_spec
        egress_spec = x
        return h

    def default():
        # The default action
        # It is set to NoAction in this case
        return a()

    def t_exact_0():
        def select_action():
            return If(MA.action(c_match) == 1,
                      a_with_control_params(BitVecVal(1, 9)),
                      If(MA.action(c_match) == 2,
                         a_with_control_params(BitVecVal(2, 9)),
                         default()  # this should be an abort of some form
                         )
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        # Right now, it is ill-defined
        key = HDR.e(h)
        return If(key == MA.match(c_match),
                  select_action(), default())

    # begin apply
    h_ret = t_exact_0()
    return h_ret, egress_spec


def control_ingress_1(h, c_match):
    # This is the emitted program after pass
    egress_spec = BitVecVal(0, 9)

    def a():
        nonlocal egress_spec
        egress_spec = BitVecVal(0, 9)
        return h

    def a_with_control_params(x):
        nonlocal egress_spec
        egress_spec = x
        return h

    def default():
        # The default action
        # It is set to NoAction in this case
        return a()

    def t_exact_0():
        def select_action():
            return If(MA.action(c_match) == 1,
                      a_with_control_params(BitVecVal(1, 9)),
                      If(MA.action(c_match) == 2,
                         a_with_control_params(BitVecVal(2, 9)),
                         default()  # this should be an abort of some form
                         )
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        # Right now, it is ill-defined
        key = HDR.e(h)
        return If(key == MA.match(c_match),
                  select_action(), default())

    # begin apply
    h_ret = t_exact_0()
    return h_ret, egress_spec


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same

    s = Solver()
    # define the header and match-action entries
    h = Const('h', HDR)
    c_match = Const('match_action', MA)
    # reduce the range of action outputs to the total number of actions
    s.add(0 < MA.action(c_match), MA.action(c_match) < 4)

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
