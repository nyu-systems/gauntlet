from z3 import *
import os

''' SOLVER '''
s = Solver()

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


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same

    bounds = [p4_return, c_t_m]
    # the equivalence equation
    tv_equiv = simplify(control_ingress_0() != control_ingress_1())
    s.add(Exists(bounds, tv_equiv))
    # tv_equiv = simplify(control_ingress_1()) != simplify(control_ingress_2())
    # s.add(Exists(bounds, tv_equiv))
    # tv_equiv = simplify(control_ingress_2()) != simplify(control_ingress_3())
    # s.add(Exists(bounds, tv_equiv))
    print(tv_equiv)
    print (s.sexpr())
    ret = s.check()
    if ret == sat:
        print (ret)
        print (s.model())
        return os.EX_PROTOCOL
    else:
        print (ret)
        return os.EX_OK


def control_ingress_0():
    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_0(func_chain, rets):
        ''' This is an action
            NoAction just returns the current header as is '''
        assigns = []
        return step(func_chain, rets, assigns)

    # @name("ingress.c.a") action c_a_0() {
    #     h.h.b = h.h.a;
    # }
    def c_a_0(func_chain, rets):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        assigns = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        # This updates an existing output variable so  we need a new version
        # The new constant is appended to the existing list of constants
        rets.append(Const("ret_%d" % new_ret, p4_output))
        # Now we create the new version by using a datatype constructor
        # The datatype constructor uses the values from the previous variable
        # version, except for the update target.
        # TODO: Make this more usable and understandable
        update = p4_output.mk_output(hdr.mk_hdr(
            hdr.a(p4_output.hdr(rets[prev_ret])),
            hdr.a(p4_output.hdr(rets[prev_ret]))),
            p4_output.egress_spec(rets[prev_ret]))
        assigns.append(rets[new_ret] == update)
        return step(func_chain, rets, assigns)

    # @name("ingress.c.t") table c_t {
    def c_t(func_chain, rets):
        ''' This is a table '''

        # actions = {
        #     c_a_0();
        #     NoAction_0();
        # }
        def actions():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This is an exclusive operation, so only Xoring is valid.
            '''
            actions = []
            actions.append(Implies(ma_c_t.action(c_t_m) == 1,
                                   c_a_0(func_chain, rets)))
            actions.append(Implies(ma_c_t.action(c_t_m) == 2,
                                   NoAction_0(func_chain, rets)))
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        # key = {
        #     h.h.a + h.h.a: exact @name("e") ;
        # }
        new_ret = len(rets)
        prev_ret = new_ret - 1
        key_matches = []
        c_t_key_0 = hdr.a(p4_output.hdr(
            rets[prev_ret])) + hdr.a(p4_output.hdr(rets[prev_ret]))
        # It is an exact match, so we use direct comparison
        key_matches.append(c_t_key_0 == ma_c_t.key_0(c_t_m))

        # default_action = NoAction_0();
        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0(func_chain, rets)

        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), actions(), default())

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []
        # c_t.apply();
        func_chain.append(c_t)

        def output_update(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            rets.append(Const("ret_%d" % new_ret, p4_output))
            update = p4_output.mk_output(
                p4_output.hdr(rets[prev_ret]), BitVecVal(0, 9))
            assigns.append(rets[new_ret] == update)
            return step(func_chain, rets, assigns)
        # sm.egress_spec = 9w0
        func_chain.append(output_update)
        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], rets=[p4_return])


def control_ingress_1():
    ''' This is the initial version of the program. '''

    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_0(func_chain, rets):
        ''' This is an action
            NoAction just returns the current header as is '''
        assigns = []
        return step(func_chain, rets, assigns)

    # @name("ingress.c.a") action c_a_0() {
    #     h.h.b = h.h.a;
    # }
    def c_a_0(func_chain, rets):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        assigns = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        # This updates an existing output variable so  we need a new version
        # The new constant is appended to the existing list of constants
        rets.append(Const("ret_%d" % new_ret, p4_output))
        # Now we create the new version by using a datatype constructor
        # The datatype constructor uses the values from the previous variable
        # version, except for the update target.
        # TODO: Make this more usable and understandable
        update = p4_output.mk_output(hdr.mk_hdr(
            hdr.a(p4_output.hdr(rets[prev_ret])),
            hdr.a(p4_output.hdr(rets[prev_ret]))),
            p4_output.egress_spec(rets[prev_ret]))
        assigns.append(rets[new_ret] == update)
        return step(func_chain, rets, assigns)

    # The key is defined in the control function
    # Practically, this is just a placeholder variable
    key_0 = BitVec("key_0", 32)  # bit<32> key_0;

    # @name("ingress.c.t") table c_t {
    def c_t(func_chain, rets):
        ''' This is a table '''

        # actions = {
        #     c_a_0();
        #     NoAction_0();
        # }
        def actions():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This is an exclusive operation, so only Xoring is valid.
            '''
            actions = []
            actions.append(Implies(ma_c_t.action(c_t_m) == 1,
                                   c_a_0(func_chain, rets)))
            actions.append(Implies(ma_c_t.action(c_t_m) == 2,
                                   NoAction_0(func_chain, rets)))
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        # key = {
        #     h.h.a + h.h.a: exact @name("e") ;
        # }
        new_ret = len(rets)
        prev_ret = new_ret - 1
        key_matches = []
        # We access the global variable key_0, which has been updated before
        c_t_key_0 = key_0
        # It is an exact match, so we use direct comparison
        key_matches.append(c_t_key_0 == ma_c_t.key_0(c_t_m))
        # default_action = NoAction_0();

        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0(func_chain, rets)

        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), actions(), default())

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []

        # {
        def block(func_chain):

            def local_update(func_chain, rets):
                ''' Updates to local variables will not play a role in the
                final output. We do not need to add new constraints. Instead,
                we update the python variable directly for later use. The
                variable is accessed using the nonlocal keyword. '''
                assigns = []
                new_ret = len(rets)
                prev_ret = new_ret - 1
                nonlocal key_0
                # key_0 is updated to have the value h.h.a + h.h.a
                key_0 = hdr.a(p4_output.hdr(
                    rets[prev_ret])) + hdr.a(p4_output.hdr(rets[prev_ret]))
                return step(func_chain, rets, assigns)
            # key_0 = h.h.a + h.h.a;
            func_chain.append(local_update)
            # c_t.apply();
            func_chain.append(c_t)
            return func_chain
        # }
        func_chain = block(func_chain)

        def output_update(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            rets.append(Const("ret_%d" % new_ret, p4_output))
            update = p4_output.mk_output(
                p4_output.hdr(rets[prev_ret]), BitVecVal(0, 9))
            assigns.append(rets[new_ret] == update)
            return step(func_chain, rets, assigns)
        # sm.egress_spec = 9w0;
        func_chain.append(output_update)

        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], rets=[p4_return])


if __name__ == '__main__':
    z3_check()
