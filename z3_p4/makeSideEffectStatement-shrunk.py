from z3 import *
import os

''' SOLVER '''
s = SolverFor("LIA")

''' HEADERS '''
# The input headers of the control pipeline
h_t = Datatype('h_t')
h_t.declare('mk_h_t', ('h', BitVecSort(8)))
h_t = h_t.create()


''' TABLES '''
''' The table constant we are matching with.
 Actually this should be a match action tuple that picks the next action
 How to implement that? Some form of array?
 Right now, we have a hacky version of integer values which mimic an enum.
 Each integer value corresponds to a specific action PER table. The number of
 available integer values is constrained. '''
t_0 = Datatype('t_0')
t_0.declare('mk_t_0', ('key_0', BitVecSort(32)), ('action', IntSort()))
t_0 = t_0.create()


''' OUTPUT '''

# the final output of the control pipeline in a single data type
p4_output = Datatype('p4_output')
p4_output.declare('mk_output',
                  ('h_t', h_t))
p4_output = p4_output.create()


''' INPUT VARIABLES AND MATCH-ACTION ENTRIES'''

# Initialize the header and match-action constraints
# These are our inputs
# Think of it as the header inputs after they have been parsed
h_t_valid = Const('h_t_valid', BoolSort())

# The output header, one variable per modification
p4_return = Const("p4_return", p4_output)

# The possible table entries
t_0_m = Const('t_0_m', t_0)
# reduce the range of action outputs to the total number of actions
# in this case we only have 2 actions
s.add(0 < t_0.action(t_0_m), t_0.action(t_0_m) < 3)


def step(func_chain, rets, assigns):
    if func_chain:
        rets = list(rets)  # do not propagate the list per step
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        assigns.append(next_fun(func_chain, rets))
    else:
        assigns.append(True)
    return And(assigns)


def control_ingress_0():
    ''' This is the initial version of the program. '''

    def NoAction_0(func_chain, rets):
        ''' This is an action
            NoAction just returns the current header as is '''
        assigns = []
        assigns.append(True)
        return step(func_chain, rets, assigns)

    def a(func_chain, rets, b_1):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        assigns = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(h_t.mk_h_t(BitVecVal(0, 8)))
        assigns.append(rets[new_ret] == assign)
        return step(func_chain, rets, assigns)

    def c_t(func_chain, rets):
        ''' This is a table '''

        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0(func_chain, rets)

        def select_action():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This is an exclusive operation, so only Xoring is valid.
            TODO: This might become really ugly with many actions.'''
            actions = []
            actions.append(Implies(t_0.action(t_0_m) == 1,
                                   a(func_chain, rets, Or(h_t_valid, True))))
            actions.append(True)
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case there is nothing to match with
        key_matches = []
        key_matches.append(True)
        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), select_action(), default())

    def apply():
        func_chain = []
        func_chain.append(c_t)  # c_t.apply();
        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], rets=[p4_return])


def control_ingress_1():
    ''' This is the initial version of the program. '''

    def NoAction_0(func_chain, rets):
        ''' This is an action
            NoAction just returns the current header as is '''
        assigns = []
        assigns.append(True)
        return step(func_chain, rets, assigns)

    b1 = BoolSort()

    def a(func_chain, rets):
        ''' This is an action
            This action creates a new header type where h is set to 0 '''
        assigns = []
        nonlocal b1
        b1 = Or(h_t_valid, True)

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(h_t.mk_h_t(BitVecVal(0, 8)))
        assigns.append(rets[new_ret] == assign)

        return step(func_chain, rets, assigns)

    def c_t(func_chain, rets):
        ''' This is a table '''

        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0(func_chain, rets)

        def select_action():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This is an exclusive operation, so only Xoring is valid.
            TODO: This might become really ugly with many actions.'''
            actions = []
            actions.append(Implies(t_0.action(t_0_m) == 1,
                                   a(func_chain, rets)))
            actions.append(True)
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case there is nothing to match with
        key_matches = []
        key_matches.append(True)
        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), select_action(), default())

    def apply():
        func_chain = []
        func_chain.append(c_t)  # c_t.apply();
        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], rets=[p4_return])


def control_ingress_2():
    ''' This is the initial version of the program. '''
    b1 = BoolSort()

    def NoAction_0(func_chain, rets):
        ''' This is an action
            NoAction just returns the current header as is '''
        assigns = []
        assigns.append(True)
        return step(func_chain, rets, assigns)

    def a(func_chain, rets):
        ''' This is an action
            This action creates a new header type where h is set to 0 '''
        assigns = []
        nonlocal b1
        b1 = Or(h_t_valid, True)

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(h_t.mk_h_t(BitVecVal(0, 8)))
        assigns.append(rets[new_ret] == assign)

        return step(func_chain, rets, assigns)

    def c_t(func_chain, rets):
        ''' This is a table '''

        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0(func_chain, rets)

        def select_action():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This is an exclusive operation, so only Xoring is valid.
            TODO: This might become really ugly with many actions.'''
            actions = []
            actions.append(Implies(t_0.action(t_0_m) == 1,
                                   a(func_chain, rets)))
            actions.append(True)
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case there is nothing to match with
        key_matches = []
        key_matches.append(True)
        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), select_action(), default())

    def apply():
        func_chain = []
        func_chain.append(c_t)  # c_t.apply();
        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], rets=[p4_return])


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same

    bounds = [p4_return, t_0_m]
    # the equivalence equation
    tv_equiv = simplify(control_ingress_0()) != simplify(control_ingress_0())
    s.add(Exists(bounds, tv_equiv))

    print(tv_equiv)
    s.add(tv_equiv)

    # print (s.sexpr())
    ret = s.check()
    if ret == sat:
        print (ret)
        print (s.model())
        return os.EX_CONFIG
    else:
        print (ret)
        return os.EX_OK


if __name__ == '__main__':
    z3_check()
