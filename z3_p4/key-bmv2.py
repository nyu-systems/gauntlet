from z3 import *


''' HEADERS '''
# The input headers of the control pipeline
hdr = Datatype('hdr')
hdr.declare('mk_hdr', ('a', BitVecSort(32)), ('b', BitVecSort(32)))
hdr = hdr.create()


''' TABLES '''
''' The table constant we are matching with.
 Actually this should be a match action tuple that picks the next action
 How to implement that? Some form of array?
 Right now, we have a hacky version of integer values which mimic an enum.
 Each integer value corresponds to a specific action PER table. The number of
 available integer values is constrained. '''
ma_c_t = Datatype('ma_c_t')
ma_c_t.declare('mk_ma_c_t', ('key_0', BitVecSort(32)), ('action', IntSort()))
ma_c_t = ma_c_t.create()


''' OUTPUT '''

# the final output of the control pipeline in a single datatype
p4_output = Datatype('p4_output')
p4_output.declare('mk_output',
                  ('hdr', hdr),
                  ('egress_spec', BitVecSort(9)))
p4_output = p4_output.create()


''' INPUT VARIABLES AND MATCH-ACTION ENTRIES'''

# Initialize the header and match-action constraints
# These are our inputs
# Think of it as the header inputs after they have been parsed
h = Const('h', hdr)
# The possible table entries
c_t_m = Const('c_t_m', ma_c_t)


def control_ingress_0(s):
    ''' This is the initial version of the program. '''

    # The output header, one variable per modification
    ret_0 = p4_output.mk_output(h, BitVecVal(0, 9))

    def c_a_0():
        # This action creates a new header type where b is set to a
        return hdr.b(p4_output.hdr(ret_0)) == hdr.a(h)

    def NoAction_0():
        ''' This is an action '''
        # NoAction just returns the current header as is
        return Var(True, BoolSort())

    def c_t():
        ''' This is a table '''
        # reduce the range of action outputs to the total number of actions
        # in this case we only have 2 actions
        s.add(0 < ma_c_t.action(c_t_m), ma_c_t.action(c_t_m) < 3)

        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0()

        def select_action():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This might become really ugly with many actions.'''
            return And(Implies(ma_c_t.action(c_t_m) == 1,
                               c_a_0()),
                       Implies(ma_c_t.action(c_t_m) == 2,
                               NoAction_0()),
                       )
        # The key of the table. In this case it is a single value
        c_t_key_0 = hdr.a(h) + hdr.a(h)
        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(c_t_key_0 == ma_c_t.key_0(c_t_m),
                  select_action(), default())

    def apply():
        # The list of assignments during the execution of the pipeline
        constraints = []

        # begin the apply pipeline
        constraints.append(c_t())
        constraints.append(p4_output.egress_spec(ret_0) == BitVecVal(0, 9))
        return constraints
    # return the apply function as sequence of logic clauses
    return And(apply())


def control_ingress_1(s):
    ''' This is the initial version of the program. '''

    # The output header, one variable per modification
    ret_0 = p4_output.mk_output(h, BitVecVal(0, 9))

    # the key is defined in the control function
    key_0 = BitVec('key_0', 32)

    def c_a_0():
        # This action creates a new header type where b is set to a
        return hdr.b(p4_output.hdr(ret_0)) == hdr.a(h)

    def NoAction_0():
        ''' This is an action '''
        # NoAction just returns the current header as is
        return Var(True, BoolSort())

    def c_t():
        ''' This is a table '''
        # reduce the range of action outputs to the total number of actions
        # in this case we only have 2 actions
        s.add(0 < ma_c_t.action(c_t_m), ma_c_t.action(c_t_m) < 3)

        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0()

        def select_action():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This might become really ugly with many actions.'''
            return And(Implies(ma_c_t.action(c_t_m) == 1,
                               c_a_0()),
                       Implies(ma_c_t.action(c_t_m) == 2,
                               NoAction_0()),
                       )
        # The key of the table. In this case it is a single value
        nonlocal key_0  # we refer to a variable in the outer scope
        c_t_key_0 = key_0
        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(c_t_key_0 == ma_c_t.key_0(c_t_m),
                  select_action(), default())

    def apply():
        # The list of assignments during the execution of the pipeline
        constraints = []

        nonlocal key_0  # we refer to a variable in the outer scope
        key_0 = hdr.a(h) + hdr.a(h)
        # begin the apply pipeline
        constraints.append(c_t())
        constraints.append(p4_output.egress_spec(ret_0) == BitVecVal(0, 9))
        return constraints
    # return the apply function as sequence of logic clauses
    return And(apply())


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
