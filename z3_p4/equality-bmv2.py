from z3 import *
import os

''' SOLVER '''
s = Solver()

''' HEADERS '''
# The input headers of the control pipeline


h = Datatype("h")
h.declare("mk_h", ('s', BitVecSort(8)),
          ('v', BitVecSort(32)))
h = h.create()


class H():

    def __init__(self):
        self.name = "h%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", h)
        self.revisions = [self.const]
        self.s = self.s_z3()
        self.v = self.v_z3()
        self.h_valid = Const('h_valid', BoolSort())

    def s_z3(self):
        return h.s(self.const)

    def v_z3(self):
        return h.v(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", h)
        self.revisions.append(self.const)

    def make(self):
        return h.mk_h(self.s, self.v)

    def set(self, lvalue, rvalue):
        z3_copy = self.make()
        update = substitute(z3_copy, (lvalue, rvalue))
        self.update()
        return update

    def isValid(self):
        return self.h_valid

    def setValid(self):
        self.h_valid == Var(True, BoolSort())


Same = Datatype("Same")
Same.declare("mk_Same", ('same', BitVecSort(8)))
Same = Same.create()


class SAME():

    def __init__(self):
        self.name = "Same%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", Same)
        self.revisions = [self.const]
        self.same = self.same_z3()
        self.Same_valid = Const('Same_valid', BoolSort())

    def same_z3(self):
        return Same.same(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", Same)
        self.revisions.append(self.const)

    def make(self):
        return Same.mk_Same(self.same)

    def set(self, lvalue, rvalue):
        z3_copy = self.make()
        update = substitute(z3_copy, (lvalue, rvalue))
        self.update()
        return update

    def isValid(self):
        return self.Same_valid

    def setValid(self):
        self.Same_valid == Var(True, BoolSort())


headers = Datatype("headers")
headers.declare(f"mk_headers",
                ('h', h), ('a_0', h), ('a_1', h), ('same', Same))
headers = headers.create()


class HEADERS():

    def __init__(self):
        self.name = "headers%s" % str(id(self))[-4:]
        self.h = H()
        self.a = [H() for i in range(2)]
        self.same = SAME()
        self.const = Const(f"{self.name}_0", headers)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", headers)
        self.revisions.append(self.const)

    def make(self):
        return headers.mk_headers(self.h.make(), self.a[0].make(),
                                  self.a[1].make(), self.same.make())

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


meta = Datatype("meta")
meta.declare(f"mk_meta")
meta = meta.create()


class META():

    def __init__(self):
        self.name = "meta%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", meta)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", meta)
        self.revisions.append(self.const)

    def make(self):
        return meta.mk_meta

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


''' TABLES '''
''' The table constant we are matching with.
 Right now, we have a hacky version of integer values which mimic an enum.
 Each integer value corresponds to a specific action PER table. The number of
 available integer values is constrained. '''
ma_c_t = Datatype('ma_c_t')
ma_c_t.declare('mk_ma_c_t', ('key_0', BitVecSort(32)), ('action', IntSort()))
ma_c_t = ma_c_t.create()


standard_metadata_t = Datatype("standard_metadata_t")
standard_metadata_t.declare(f"mk_standard_metadata_t",
                            ('egress_spec', BitVecSort(9)),
                            )
standard_metadata_t = standard_metadata_t.create()


''' TABLES '''
''' Standard metadata definitions. These are typically defined by the model
    imported on top of the file.'''


class STANDARD_METADATA_T():

    def __init__(self):
        self.name = "standard_metadata_t%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", standard_metadata_t)
        self.revisions = [self.const]

        self.egress_spec = self.egress_spec_z3()

    def egress_spec_z3(self):
        return standard_metadata_t.egress_spec(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", standard_metadata_t)
        self.revisions.append(self.const)

    def make(self):
        return standard_metadata_t.mk_standard_metadata_t(
            self.egress_spec,
        )

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


''' INPUT VARIABLES AND MATCH-ACTION ENTRIES'''

''' Initialize the header and match-action constraints
 These are our inputs and outputs
 Think of it as the header inputs after they have been parsed'''

''' OUTPUT '''
''' The final output of the control pipeline in a single data type.
 This corresponds to the arguments of the control function'''
inouts = Datatype("inouts")
inouts.declare(f"mk_inouts", ('hdr', headers), ('meta', meta),
               ('stdmeta', standard_metadata_t))
inouts = inouts.create()


class INOUTS():

    def __init__(self):
        self.name = "inouts%s" % str(id(self))[-4:]
        self.hdr = HEADERS()
        self.meta = META()
        self.stdmeta = STANDARD_METADATA_T()
        self.const = Const(f"{self.name}_0", inouts)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", inouts)
        self.revisions.append(self.const)

    def make(self):
        return inouts.mk_inouts(self.hdr.make(), self.meta.make(),
                                self.stdmeta.make())

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


''' INPUT CONTROL '''
# The possible table entries


def step(func_chain, inouts, assigns):
    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        inouts = copy.deepcopy(inouts)  # emulate pass-by-value behavior
        assigns.append(next_fun(func_chain, inouts))
    else:
        assigns.append(True)
    return And(assigns)


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same

    inouts = INOUTS()
    bounds = [inouts.const]
    # the equivalence equation
    tv_equiv = control_ingress_0(inouts) != control_ingress_1(inouts)
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


def control_ingress_0(inouts):
    ''' This is the initial version of the program. '''

    tmp = [Const("tmp_%d" % i, h) for i in range(2)]

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []

        # hdr.same.setValid();
        inouts.hdr.same.setValid()

        def output_update(func_chain, inouts):
            assigns = []
            inouts.hdr.same.same = BitVecVal(0, 8)
            update = inouts.set(inouts.hdr.same.same, BitVecVal(0, 8))
            assigns.append(inouts.const == update)
            return step(func_chain, inouts, assigns)
        # hdr.same.same = 8w0;
        func_chain.append(output_update)

        def output_update(func_chain, inouts):
            assigns = []
            inouts.stdmeta.egress_spec = BitVecVal(0, 9)
            update = inouts.set(inouts.stdmeta.egress_spec, BitVecVal(0, 9))
            assigns.append(inouts.const == update)
            return step(func_chain, inouts, assigns)
        # stdmeta.egress_spec = 9w0;
        func_chain.append(output_update)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            condition = (inouts.hdr.h.s == inouts.hdr.a[0].s)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = inouts.hdr.same.same | BitVecVal(1, 8)
                update = inouts.set(
                    inouts.hdr.same.same, inouts.hdr.same.same | BitVecVal(1, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            condition = (inouts.hdr.h.v == inouts.hdr.a[0].v)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = inouts.hdr.same.same | BitVecVal(2, 8)
                update = inouts.set(
                    inouts.hdr.same.same, inouts.hdr.same.same | BitVecVal(2, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            # !hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v
            condition = And(And(And(Or(And(Not(inouts.hdr.h.isValid()),
                                           Not(inouts.hdr.a[0].isValid())),
                                       inouts.hdr.h.isValid()),
                                    inouts.hdr.a[0].isValid()),
                                inouts.hdr.h.s == inouts.hdr.a[0].s),
                            inouts.hdr.h.v == inouts.hdr.a[0].v)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = inouts.hdr.same.same | BitVecVal(4, 8)
                update = inouts.set(
                    inouts.hdr.same.same, inouts.hdr.same.same | BitVecVal(4, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def local_update(func_chain, inouts):
            assigns = []
            nonlocal tmp
            tmp[0] = inouts.hdr.h
            return step(func_chain, inouts, assigns)
        # mp[0] = hdr.h;
        func_chain.append(local_update)

        def local_update(func_chain, inouts):
            assigns = []
            nonlocal tmp
            tmp[1] = inouts.hdr.a[0]
            return step(func_chain, inouts, assigns)
        # mp[0] = hdr.h;
        func_chain.append(local_update)

        return func_chain

    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], inouts=inouts)


def control_ingress_1(inouts):
    ''' This is the initial version of the program. '''

    tmp = [Const("tmp_%d" % i, h) for i in range(2)]

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []

        # hdr.same.setValid();
        inouts.hdr.same.setValid()

        def output_update(func_chain, inouts):
            assigns = []
            inouts.hdr.same.same = BitVecVal(0, 8)
            update = inouts.set(inouts.hdr.same.same, BitVecVal(0, 8))
            assigns.append(inouts.const == update)
            return step(func_chain, inouts, assigns)
        # hdr.same.same = 8w0;
        func_chain.append(output_update)

        def output_update(func_chain, inouts):
            assigns = []
            inouts.stdmeta.egress_spec = BitVecVal(0, 9)
            update = inouts.set(inouts.stdmeta.egress_spec, BitVecVal(0, 9))
            assigns.append(inouts.const == update)
            return step(func_chain, inouts, assigns)
        # stdmeta.egress_spec = 9w0;
        func_chain.append(output_update)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            condition = (inouts.hdr.h.s == inouts.hdr.a[0].s)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = BitVecVal(0, 8) | BitVecVal(1, 8)
                update = inouts.set(
                    inouts.hdr.same.same, BitVecVal(0, 8) | BitVecVal(1, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            condition = (inouts.hdr.h.v == inouts.hdr.a[0].v)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = inouts.hdr.same.same | BitVecVal(2, 8)
                update = inouts.set(
                    inouts.hdr.same.same, inouts.hdr.same.same | BitVecVal(2, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            # !hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v
            condition = And(And(And(Or(And(Not(inouts.hdr.h.isValid()),
                                           Not(inouts.hdr.a[0].isValid())),
                                       inouts.hdr.h.isValid()),
                                    inouts.hdr.a[0].isValid()),
                                inouts.hdr.h.s == inouts.hdr.a[0].s),
                            inouts.hdr.h.v == inouts.hdr.a[0].v)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = inouts.hdr.same.same | BitVecVal(4, 8)
                update = inouts.set(
                    inouts.hdr.same.same, inouts.hdr.same.same | BitVecVal(4, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def local_update(func_chain, inouts):
            assigns = []
            nonlocal tmp
            tmp[0] = inouts.hdr.h
            return step(func_chain, inouts, assigns)
        # mp[0] = hdr.h;
        func_chain.append(local_update)

        def local_update(func_chain, inouts):
            assigns = []
            nonlocal tmp
            tmp[1] = inouts.hdr.a[0]
            return step(func_chain, inouts, assigns)
        # mp[0] = hdr.h;
        func_chain.append(local_update)

        return func_chain

    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], inouts=inouts)


def control_ingress_2(inouts):
    ''' This is the initial version of the program. '''

    tmp = [Const("tmp_%d" % i, h) for i in range(2)]

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []

        # hdr.same.setValid();
        inouts.hdr.same.setValid()

        def output_update(func_chain, inouts):
            assigns = []
            inouts.hdr.same.same = BitVecVal(0, 8)
            update = inouts.set(inouts.hdr.same.same, BitVecVal(0, 8))
            assigns.append(inouts.const == update)
            return step(func_chain, inouts, assigns)
        # hdr.same.same = 8w0;
        func_chain.append(output_update)

        def output_update(func_chain, inouts):
            assigns = []
            inouts.stdmeta.egress_spec = BitVecVal(0, 9)
            update = inouts.set(inouts.stdmeta.egress_spec, BitVecVal(0, 9))
            assigns.append(inouts.const == update)
            return step(func_chain, inouts, assigns)
        # stdmeta.egress_spec = 9w0;
        func_chain.append(output_update)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            condition = (inouts.hdr.h.s == inouts.hdr.a[0].s)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = BitVecVal(1, 8)
                update = inouts.set(
                    inouts.hdr.same.same, BitVecVal(1, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            condition = (inouts.hdr.h.v == inouts.hdr.a[0].v)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = inouts.hdr.same.same | BitVecVal(2, 8)
                update = inouts.set(
                    inouts.hdr.same.same, inouts.hdr.same.same | BitVecVal(2, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def if_block(func_chain, inouts):

            # If blocks track two expression lists for the if and the else case
            # if (hdr.h.s == hdr.a[0].s)
            # !hdr.h.isValid() && !hdr.a[0].isValid() || hdr.h.isValid() && hdr.a[0].isValid() && hdr.h.s == hdr.a[0].s && hdr.h.v == hdr.a[0].v
            condition = And(And(And(Or(And(Not(inouts.hdr.h.isValid()),
                                           Not(inouts.hdr.a[0].isValid())),
                                       inouts.hdr.h.isValid()),
                                    inouts.hdr.a[0].isValid()),
                                inouts.hdr.h.s == inouts.hdr.a[0].s),
                            inouts.hdr.h.v == inouts.hdr.a[0].v)
            if_list = list(func_chain)
            else_list = list(func_chain)
            assignments = []

            def output_update(func_chain, inouts):
                assigns = []
                inouts.hdr.same.same = inouts.hdr.same.same | BitVecVal(4, 8)
                update = inouts.set(
                    inouts.hdr.same.same, inouts.hdr.same.same | BitVecVal(4, 8))
                assigns.append(inouts.const == update)
                return step(func_chain, inouts, assigns)
            if_list.append(output_update)

            return If(condition, step(if_list, inouts, assignments),
                      step(else_list, inouts, assignments))
        func_chain.append(if_block)

        def local_update(func_chain, inouts):
            assigns = []
            nonlocal tmp
            tmp[0] = inouts.hdr.h
            return step(func_chain, inouts, assigns)
        # mp[0] = hdr.h;
        func_chain.append(local_update)

        def local_update(func_chain, inouts):
            assigns = []
            nonlocal tmp
            tmp[1] = inouts.hdr.a[0]
            return step(func_chain, inouts, assigns)
        # mp[0] = hdr.h;
        func_chain.append(local_update)

        return func_chain

    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], inouts=inouts)


if __name__ == '__main__':
    z3_check()
