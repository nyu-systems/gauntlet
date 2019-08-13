from p4z3_base import *
import os
import operator

''' Model imports at the top of the p4 file '''
from v1model import *


''' HEADERS '''
# The input headers of the control pipeline
# Datatypes have to be declared outside the type object because of issues with
# deepcopy()

# header hdr {
#     bit<32> a;
#     bit<32> b;
# }
Ethernet_h = Datatype("Ethernet_h")
Ethernet_h.declare("mk_Ethernet_h", ('dstAddr', BitVecSort(48)),
                   ('srcAddr', BitVecSort(48)), ('etherType', BitVecSort(16)))
Ethernet_h = Ethernet_h.create()


class ETHERNET_H():

    def __init__(self):
        self.name = "Ethernet_h%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", Ethernet_h)
        self.revisions = [self.const]
        self.dstAddr = self.dstAddr_z3()
        self.srcAddr = self.srcAddr_z3()
        self.etherType = self.etherType_z3()
        self.valid = Const('Ethernet_h_valid', BoolSort())

    def dstAddr_z3(self):
        return Ethernet_h.dstAddr(self.const)

    def srcAddr_z3(self):
        return Ethernet_h.srcAddr(self.const)

    def etherType_z3(self):
        return Ethernet_h.etherType(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", Ethernet_h)
        self.revisions.append(self.const)

    def make(self):
        return Ethernet_h.mk_Ethernet_h(self.dstAddr, self.srcAddr,
                                        self.etherType)

    def set(self, lstring, rvalue):
        # update the internal representation of the attribute
        lvalue = operator.attrgetter(lstring)(self)
        prefix, suffix = lstring.rsplit(".", 1)
        target_class = operator.attrgetter(prefix)(self)
        setattr(target_class, suffix, rvalue)
        # generate a new version of the z3 datatype
        copy = self.make()
        # update the SSA version
        self.update()
        # return the update expression
        return (self.const == copy)

    def isValid(self):
        return self.valid

    def setValid(self):
        self.valid = True

    def setInvalid(self):
        self.valid = False


''' STRUCTS '''
# Data structures that were declared globally

# struct Headers {
#     Ethernet_h h;
# }
headers = Datatype("headers")
headers.declare(f"mk_headers", ('ethernet', Ethernet_h))
headers = headers.create()


class HEADERS():

    def __init__(self):
        self.name = "headers%s" % str(id(self))[-4:]
        self.ethernet = ETHERNET_H()
        self.const = Const(f"{self.name}_0", headers)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", headers)
        self.revisions.append(self.const)

    def make(self):
        return headers.mk_headers(self.ethernet.make())

    def set(self, lstring, rvalue):
        # update the internal representation of the attribute
        lvalue = operator.attrgetter(lstring)(self)
        prefix, suffix = lstring.rsplit(".", 1)
        target_class = operator.attrgetter(prefix)(self)
        setattr(target_class, suffix, rvalue)
        # generate a new version of the z3 datatype
        copy = self.make()
        # update the SSA version
        self.update()
        # return the update expression
        return (self.const == copy)


# struct Meta {
# }
meta = Datatype("meta")
meta.declare(f"mk_meta", ('a', BitVecSort(4)), ('b', BitVecSort(4)))
meta = meta.create()


class META():

    def __init__(self):
        self.name = "meta%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", meta)
        self.revisions = [self.const]
        self.a = self.a_z3()
        self.b = self.b_z3()

    def a_z3(self):
        return meta.a(self.const)

    def b_z3(self):
        return meta.b(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", meta)
        self.revisions.append(self.const)

    def make(self):
        return meta.mk_meta(self.a, self.b)

    def set(self, lstring, rvalue):
        # update the internal representation of the attribute
        lvalue = operator.attrgetter(lstring)(self)
        prefix, suffix = lstring.rsplit(".", 1)
        target_class = operator.attrgetter(prefix)(self)
        setattr(target_class, suffix, rvalue)
        # generate a new version of the z3 datatype
        copy = self.make()
        # update the SSA version
        self.update()
        # return the update expression
        return (self.const == copy)


''' OUTPUT '''
''' Initialize the header  These are our inputs and outputs
 Think of it as the header inputs after they have been parsed.
 The final output of the control pipeline in a single data type.
 This corresponds to the arguments of the control function'''

# control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm)
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

    def set(self, lstring, rvalue):
        # update the internal representation of the attribute
        lvalue = operator.attrgetter(lstring)(self)
        prefix, suffix = lstring.rsplit(".", 1)
        target_class = operator.attrgetter(prefix)(self)
        setattr(target_class, suffix, rvalue)
        # generate a new version of the z3 datatype
        copy = self.make()
        # update the SSA version
        self.update()
        return (self.const == copy)


def control_ingress_0(s, inouts):

    def NoAction_0(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def a1(func_chain, inouts):
        sub_chain = []

        def output_update(func_chain, inouts):
            assign = BitVecVal(1, 8)
            rval = slice_assign(
                inouts.hdr.ethernet.srcAddr, assign, (47, 40))
            expr = inouts.set("hdr.ethernet.srcAddr", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def a2(func_chain, inouts):
        sub_chain = []

        def output_update(func_chain, inouts):
            assign = BitVecVal(2, 8)
            rval = slice_assign(
                inouts.hdr.ethernet.srcAddr, assign, (47, 40))
            expr = inouts.set("hdr.ethernet.srcAddr", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def a3(func_chain, inouts):
        sub_chain = []

        def output_update(func_chain, inouts):
            assign = BitVecVal(3, 8)
            rval = slice_assign(
                inouts.hdr.ethernet.srcAddr, assign, (47, 40))
            expr = inouts.set("hdr.ethernet.srcAddr", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def a4(func_chain, inouts):
        sub_chain = []

        def output_update(func_chain, inouts):
            assign = BitVecVal(4, 8)
            rval = slice_assign(
                inouts.hdr.ethernet.srcAddr, assign, (47, 40))
            expr = inouts.set("hdr.ethernet.srcAddr", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    class t1_0():

        def __init__(self):
            self.ma_t1_0 = Datatype('ma_t1_0')
            self.ma_t1_0.declare('mk_ma_t1_0', ('key_0', BitVecSort(48)),
                                 ('action', IntSort()))
            self.ma_t1_0 = self.ma_t1_0.create()
            # The possible table entries as constant
            self.t1_0_m = Const('t1_0_m', self.ma_t1_0)
            self.actions = {
                a1: 1,
                a2: 2,
                a3: 3,
                a4: 4,
                NoAction_0: 5,
            }
            self.default = NoAction_0

        def table_action(self, func_chain, inouts):
            actions = []
            for f_a, f_id in self.actions.items():
                expr = Implies(self.ma_t1_0.action(self.t1_0_m) == f_id,
                               f_a(func_chain, inouts))
                actions.append(expr)
            return And(*actions)

        def table_match(self, inouts):
            key_matches = []
            t1_0_key_0 = inouts.hdr.ethernet.dstAddr
            # It is an exact match, so we use direct comparison
            key_matches.append(t1_0_key_0 == self.ma_t1_0.key_0(self.t1_0_m))
            return And(key_matches)

        def action_run(self, inouts):
            return If(self.table_match(inouts),
                      self.ma_t1_0.action(self.t1_0_m),
                      self.actions[self.default])

        def apply(self, func_chain, inouts):
            return If(self.table_match(inouts), self.table_action(func_chain, inouts), self.default(func_chain, inouts))

    t1_0 = t1_0()

    def apply(func_chain, inouts):
        sub_chain = []

        sub_chain.append(t1_0.apply)

        def switch_block(sub_chain, inouts):
            cases = []
            switch = t1_0.action_run(inouts)

            def case_block(sub_chain, inouts):
                sub_chain = []

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 1, case_block(func_chain, inouts))
            cases.append(case)

            def case_block(sub_chain, inouts):
                sub_chain = []

                def output_update(func_chain, inouts):
                    assign = BitVecVal(2, 8)
                    rval = slice_assign(
                        inouts.hdr.ethernet.srcAddr, assign, (39, 32))
                    expr = inouts.set("hdr.ethernet.srcAddr", rval)
                    return step(func_chain, inouts, expr)
                sub_chain.append(output_update)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 1, case_block(func_chain, inouts))
            cases.append(case)

            def case_block(sub_chain, inouts):
                sub_chain = []

                def output_update(func_chain, inouts):
                    assign = BitVecVal(3, 8)
                    rval = slice_assign(
                        inouts.hdr.ethernet.srcAddr, assign, (39, 32))
                    expr = inouts.set("hdr.ethernet.srcAddr", rval)
                    return step(func_chain, inouts, expr)
                sub_chain.append(output_update)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 2, case_block(func_chain, inouts))
            cases.append(case)

            def case_block(sub_chain, inouts):
                sub_chain = []

                def output_update(func_chain, inouts):
                    assign = BitVecVal(4, 8)
                    rval = slice_assign(
                        inouts.hdr.ethernet.srcAddr, assign, (39, 32))
                    expr = inouts.set("hdr.ethernet.srcAddr", rval)
                    return step(func_chain, inouts, expr)
                sub_chain.append(output_update)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 3, case_block(func_chain, inouts))
            cases.append(case)

            def case_block(sub_chain, inouts):
                sub_chain = []

                def output_update(func_chain, inouts):
                    assign = BitVecVal(5, 8)
                    rval = slice_assign(
                        inouts.hdr.ethernet.srcAddr, assign, (39, 32))
                    expr = inouts.set("hdr.ethernet.srcAddr", rval)
                    return step(func_chain, inouts, expr)
                sub_chain.append(output_update)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 4, case_block(func_chain, inouts))
            cases.append(case)
            return And(*cases)
        sub_chain.append(switch_block)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)
    return step(func_chain=[apply], inouts=inouts)


def control_ingress_1(s, inouts):
    def NoAction_0(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def a1(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def a2(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def a3(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def a4(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_0(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    class t1_0():

        def __init__(self):
            self.ma_t1_0 = Datatype('ma_t1_0')
            self.ma_t1_0.declare('mk_ma_t1_0', ('key_0', BitVecSort(48)),
                                 ('action', IntSort()))
            self.ma_t1_0 = self.ma_t1_0.create()
            # The possible table entries as constant
            self.t1_0_m = Const('t1_0_m', self.ma_t1_0)
            self.actions = {
                a1: 1,
                a2: 2,
                a3: 3,
                a4: 4,
                NoAction_0: 5,
            }
            self.default = NoAction_0

        def table_action(self, func_chain, inouts):
            actions = []
            for f_a, f_id in self.actions.items():
                expr = Implies(self.ma_t1_0.action(self.t1_0_m) == f_id,
                               f_a(func_chain, inouts))
                actions.append(expr)
            return And(*actions)

        def table_match(self, func_chain, inouts):
            key_matches = []
            t1_0_key_0 = inouts.hdr.ethernet.dstAddr
            # It is an exact match, so we use direct comparison
            key_matches.append(t1_0_key_0 == self.ma_t1_0.key_0(self.t1_0_m))
            return And(key_matches)

        def action_run(self, inouts):
            return If(self.table_match(inouts),
                      self.ma_t1_0.action(self.t1_0_m),
                      self.actions[self.default])

        def apply(self, func_chain, inouts):
            return If(self.table_match(inouts), self.table_action(func_chain, inouts), self.default(func_chain, inouts))

    t1_0 = t1_0()

    def apply(func_chain, inouts):
        sub_chain = []

        sub_chain.append(t1_0.apply)

        def switch_block(sub_chain, inouts):
            cases = []
            switch = t1_0.action_run(inouts)

            def case_block(sub_chain, inouts):
                sub_chain = []

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 1, case_block(func_chain, inouts))
            cases.append(case)

            def case_block(sub_chain, inouts):
                sub_chain = []

                def output_update(func_chain, inouts):
                    assign = BitVecVal(2, 8)
                    rval = slice_assign(
                        inouts.hdr.ethernet.srcAddr, assign, (39, 32))
                    expr = inouts.set("hdr.ethernet.srcAddr", rval)
                    return step(func_chain, inouts, expr)
                sub_chain.append(output_update)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 1, case_block(func_chain, inouts))
            cases.append(case)

            def case_block(sub_chain, inouts):
                sub_chain = []

                def output_update(func_chain, inouts):
                    assign = BitVecVal(3, 8)
                    rval = slice_assign(
                        inouts.hdr.ethernet.srcAddr, assign, (39, 32))
                    expr = inouts.set("hdr.ethernet.srcAddr", rval)
                    return step(func_chain, inouts, expr)
                sub_chain.append(output_update)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 2, case_block(func_chain, inouts))
            cases.append(case)

            def case_block(sub_chain, inouts):
                sub_chain = []

                def output_update(func_chain, inouts):
                    assign = BitVecVal(4, 8)
                    rval = slice_assign(
                        inouts.hdr.ethernet.srcAddr, assign, (39, 32))
                    expr = inouts.set("hdr.ethernet.srcAddr", rval)
                    return step(func_chain, inouts, expr)
                sub_chain.append(output_update)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 3, case_block(func_chain, inouts))
            cases.append(case)

            def case_block(sub_chain, inouts):
                sub_chain = []

                def output_update(func_chain, inouts):
                    assign = BitVecVal(5, 8)
                    rval = slice_assign(
                        inouts.hdr.ethernet.srcAddr, assign, (39, 32))
                    expr = inouts.set("hdr.ethernet.srcAddr", rval)
                    return step(func_chain, inouts, expr)
                sub_chain.append(output_update)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(switch == 4, case_block(func_chain, inouts))
            cases.append(case)
            return And(*cases)
        sub_chain.append(switch_block)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)
    return step(func_chain=[apply], inouts=inouts)


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    s = Solver()

    inouts = INOUTS()
    bounds = [inouts.const]
    # the equivalence equation
    tv_equiv = simplify(control_ingress_0(s, inouts) !=
                        control_ingress_1(s, inouts))
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


if __name__ == '__main__':
    z3_check()
