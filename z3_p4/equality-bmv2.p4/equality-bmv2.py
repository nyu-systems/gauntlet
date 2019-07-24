from z3 import *
import os

''' SOLVER '''
s = Solver()

''' HEADERS '''
# The input headers of the control pipeline
H = Datatype('H')
H.declare('mk_H', ('s', BitVecSort(8)), ('v', BitVecSort(32)))
H = H.create()

Same = Datatype('Same')
Same.declare('mk_Same', ('same', BitVecSort(8)))
Same = Same.create()

headers = Datatype('headers')
headers.declare('mk_headers',
                ('h', H),
                ('a_0', H),
                ('a_1', H),
                ('same', Same)
                )
headers = headers.create()

''' TABLES '''
''' The table constant we are matching with.
 Actually this should be a match action tuple that picks the next action
 How to implement that? Some form of array?
 Right now, we have a hacky version of integer values which mimic an enum.
 Each integer value corresponds to a specific action PER table. The number of
 available integer values is constrained. '''


''' OUTPUT '''

# the final output of the control pipeline in a single data type
p4_output = Datatype('p4_output')
p4_output.declare('mk_output',
                  ('headers', headers),
                  ('egress_spec', BitVecSort(9)))
p4_output = p4_output.create()


''' INPUT VARIABLES AND MATCH-ACTION ENTRIES'''

# Initialize the header and match-action constraints
# These are our inputs
# Think of it as the header inputs after they have been parsed
H_valid = Const('H_valid', BoolSort())
Same_valid = Const('Same_valid', BoolSort())

# The output header, one variable per modification
p4_return = Const("p4_return", p4_output)

# The possible table entries
# reduce the range of action outputs to the total number of actions
# in this case we only have 2 actions


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

    bounds = [p4_return]
    # the equivalence equation
    tv_equiv = simplify(control_ingress_0() != control_ingress_0())
    s.add(Exists(bounds, tv_equiv))

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
    tmp_arr = [Const("tmp_%d" % i, H) for i in range(2)]

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []

        def setValid(func_chain, rets):
            assigns = []
            assigns.append(Same_valid == True)
            return step(func_chain, rets, assigns)
        # hdr.same.setValid();
        func_chain.append(setValid)

        def output_update(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            rets.append(Const("ret_%d" % new_ret, p4_output))
            update = p4_output.mk_output(
                p4_output.headers(rets[prev_ret]), BitVecVal(0, 9))
            assigns.append(rets[new_ret] == update)
            return step(func_chain, rets, assigns)
        # sm.egress_spec = 9w0
        func_chain.append(output_update)

        def if_block(func_chain, rets):

            # If blocks track two expression lists for the if and the else case
            new_ret = len(rets)
            prev_ret = new_ret - 1
            condition = (H.s(headers.h(p4_output.headers(rets[prev_ret])))
                         == H.s(headers.a_0(p4_output.headers(rets[prev_ret]))))
            if_list = []
            else_list = []
            assignments = []
            else_list = []

            def output_update(func_chain, rets):
                assigns = []
                new_ret = len(rets)
                prev_ret = new_ret - 1
                rets.append(Const("ret_%d" % new_ret, p4_output))
                update = p4_output.mk_output(
                    p4_output.headers(rets[prev_ret]), BitVecVal(0, 9))
                assigns.append(rets[new_ret] == update)
                return step(func_chain, rets, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, rets, assignments),
                      step(else_list, rets, assignments))
        func_chain.append(if_block)

        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], rets=[p4_return])


if __name__ == '__main__':
    z3_check()
