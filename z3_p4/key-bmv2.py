from z3 import *
import os

''' SOLVER '''
s = SolverFor("LIA")

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

# the final output of the control pipeline in a single data type
p4_output = Datatype('p4_output')
p4_output.declare('mk_output',
                  ('hdr', hdr),
                  ('egress_spec', BitVecSort(9)))
p4_output = p4_output.create()


''' INPUT VARIABLES AND MATCH-ACTION ENTRIES'''

# Initialize the header and match-action constraints
# These are our inputs
# Think of it as the header inputs after they have been parsed
h_valid = Const('h_valid', BoolSort())

# The output header, one variable per modification
p4_return = Const("p4_return", p4_output)

# The possible table entries
c_t_m = Const('c_t_m', ma_c_t)
# reduce the range of action outputs to the total number of actions
# in this case we only have 2 actions
s.add(0 < ma_c_t.action(c_t_m), ma_c_t.action(c_t_m) < 3)


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

    def c_a_0(func_chain, rets):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        assigns = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(hdr.mk_hdr(
            hdr.a(p4_output.hdr(rets[prev_ret])),
            hdr.a(p4_output.hdr(rets[prev_ret]))),
            p4_output.egress_spec(rets[prev_ret]))
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
            actions.append(Implies(ma_c_t.action(c_t_m) == 1,
                                   c_a_0(func_chain, rets)))
            actions.append(Implies(ma_c_t.action(c_t_m) == 2,
                                   NoAction_0(func_chain, rets)))
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        new_ret = len(rets)
        prev_ret = new_ret - 1
        key_matches = []
        c_t_key_0 = hdr.a(p4_output.hdr(
            rets[prev_ret])) + hdr.a(p4_output.hdr(rets[prev_ret]))
        key_matches.append(c_t_key_0 == ma_c_t.key_0(c_t_m))
        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), select_action(), default())

    def apply():
        func_chain = []
        func_chain.append(c_t)  # c_t.apply();

        def output_update(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            rets.append(Const("ret_%d" % new_ret, p4_output))
            update = p4_output.mk_output(
                p4_output.hdr(rets[prev_ret]), BitVecVal(0, 9))
            assigns.append(rets[new_ret] == update)
            return step(func_chain, rets, assigns)
        # The list of assigns during the execution of the pipeline
        func_chain.append(output_update)  # sm.egress_spec = 9w0;
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

    def c_a_0(func_chain, rets):
        ''' This is an action
            This action creates a new header type where b is set to a '''

        assigns = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        update = p4_output.mk_output(hdr.mk_hdr(
            hdr.a(p4_output.hdr(rets[prev_ret])),
            hdr.a(p4_output.hdr(rets[prev_ret]))),
            p4_output.egress_spec(rets[prev_ret]))
        assigns.append(rets[new_ret] == update)
        return step(func_chain, rets, assigns)

    # the key is defined in the control function
    key_0 = BitVec("key_0", 32)  # bit<32> key_0;

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
            This is an exclusive operation, so only XORing is valid.
            TODO: This might become really ugly with many actions.'''
            actions = []
            actions.append(Implies(ma_c_t.action(c_t_m) == 1,
                                   c_a_0(func_chain, rets)))
            actions.append(Implies(ma_c_t.action(c_t_m) == 2,
                                   NoAction_0(func_chain, rets)))
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        key_matches = []
        c_t_key_0 = key_0
        key_matches.append(c_t_key_0 == ma_c_t.key_0(c_t_m))
        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), select_action(), default())

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []

        def local_assign(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            nonlocal key_0
            key_0 = hdr.a(p4_output.hdr(
                rets[prev_ret])) + hdr.a(p4_output.hdr(rets[prev_ret]))
            return step(func_chain, rets, assigns)

        func_chain.append(local_assign)  # key_0 = h.h.a + h.h.a;
        func_chain.append(c_t)  # c_t.apply();

        def output_update(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            rets.append(Const("ret_%d" % new_ret, p4_output))
            update = p4_output.mk_output(
                p4_output.hdr(rets[prev_ret]), BitVecVal(0, 9))
            assigns.append(rets[new_ret] == update)
            return step(func_chain, rets, assigns)
        func_chain.append(output_update)  # sm.egress_spec = 9w0;

        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], rets=[p4_return])


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same

    bounds = [p4_return, c_t_m]
    # the equivalence equation
    tv_equiv = simplify(control_ingress_0()) != simplify(control_ingress_1())
    s.add(Exists(bounds, tv_equiv))

    print(tv_equiv)
    s.add(tv_equiv)

    # print (s.sexpr())
    ret = s.check()
    if ret == sat:
        print (ret)
        print (s.model())
        return os.EX_ERR
    else:
        print (ret)
        return os.EX_OK


if __name__ == '__main__':
    z3_check()
