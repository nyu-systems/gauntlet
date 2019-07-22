from z3 import *
import os

''' SOLVER '''
s = Solver()


''' HEADERS '''
# The input headers of the control pipeline
Hdr = Datatype('Hdr')
Hdr.declare('mk_Hdr',
            ('fA', BitVecSort(32)), ('fB', BitVecSort(16)),
            ('fC', BitVecSort(16)), ('fD', BitVecSort(16)),
            ('fE', BitVecSort(16)), ('fF', BitVecSort(32)),
            ('fG', BitVecSort(8))
            )
Hdr = Hdr.create()

FieldList1_t = Datatype('FieldList1_t')
FieldList1_t.declare('mk_FieldList1_t',
                     ('a', BitVecSort(8)), ('b', BitVecSort(16)))
FieldList1_t = FieldList1_t.create()

FieldList2_t = Datatype('FieldList2_t')
FieldList2_t.declare('mk_FieldList2_t',
                     ('a', BitVecSort(16)), ('b', BitVecSort(16)),
                     ('c', BitVecSort(32)))
FieldList2_t = FieldList2_t.create()


FieldLists_t = Datatype('FieldLists_t')
FieldLists_t.declare('mk_FieldLists_t',
                     ('fl1', FieldList1_t), ('fl2', FieldList2_t))
FieldLists_t = FieldLists_t.create()

Hash_T = DeclareSort('Hash_T')
I = DeclareSort('I')
Hash_get = Function('Hash_get', I, Hash_T)


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
                  ('Hdr', Hdr),
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
# reduce the range of action outputs to the total number of actions


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
    fl1_0 = Const("fl1_0", FieldList1_t)  # FieldList1_t fl2_0;
    fl2_0 = Const("fl2_0", FieldList2_t)  # FieldList2_t fl2_0;
    output_0 = BitVec("output_0", 16)  # bit<16> output_0;
    tmp = BitVec("tmp", 16)  # bit<16> tmp;

    def apply():
        func_chain = []

        def local_assign(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            nonlocal fl1_0
            fl1_0 = FieldList1_t.mk_FieldList1_t(Extract(31, 24, Hdr.fA(p4_output.Hdr(
                rets[prev_ret]))), Hdr.fB(p4_output.Hdr(
                    rets[prev_ret])))
            return step(func_chain, rets, assigns)
        # fl1_0 = { hdr.h.fA[31:24], hdr.h.fB };
        func_chain.append(local_assign)

        def local_assign(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            nonlocal fl2_0
            fl2_0 = FieldList2_t.mk_FieldList2_t(
                Hdr.fB(p4_output.Hdr(rets[prev_ret])),
                Hdr.fC(p4_output.Hdr(rets[prev_ret])),
                Hdr.fA(p4_output.Hdr(rets[prev_ret])))
            return step(func_chain, rets, assigns)
        # fl2_0 = { hdr.h.fB, hdr.h.fC, hdr.h.fA };
        func_chain.append(local_assign)

        def local_assign(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            nonlocal tmp
            Hash_get = Function('Hash_get', FieldLists_t, BitVecSort(16))
            tmp = Hash_get(FieldLists_t.mk_FieldLists_t(
                fl1_0, fl2_0))
            return step(func_chain, rets, assigns)
        # tmp = hash1_0.get<FieldLists_t>(FieldLists_t {fl1 = fl1_0,fl2 = fl2_0});
        func_chain.append(local_assign)

        def local_assign(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            nonlocal output_0
            output_0 = tmp
            return step(func_chain, rets, assigns)
        # output_0 = tmp;
        func_chain.append(local_assign)

        def output_update(func_chain, rets):
            assigns = []
            new_ret = len(rets)
            prev_ret = new_ret - 1
            rets.append(Const("ret_%d" % new_ret, p4_output))
            update = p4_output.mk_output(
                p4_output.Hdr(rets[prev_ret]), Extract(8, 0, output_0))
            assigns.append(rets[new_ret] == update)
            return step(func_chain, rets, assigns)
        func_chain.append(output_update)  # sm.egress_spec = (bit<9>)output_0;
        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], rets=[p4_return])


if __name__ == '__main__':
    z3_check()
