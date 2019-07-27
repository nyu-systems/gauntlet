from z3 import *
import os

''' SOLVER '''
s = Solver()

''' HEADERS '''
# The input headers of the control pipeline


ethernet_t = Datatype("ethernet_t")
ethernet_t.declare("mk_ethernet_t", ('dstAddr', BitVecSort(48)),
                   ('srcAddr', BitVecSort(48)), ('etherType', BitVecSort(16)))
ethernet_t = ethernet_t.create()


class ETHERNET_T():

    def __init__(self):
        self.name = "ethernet_t%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", ethernet_t)
        self.revisions = [self.const]
        self.dstAddr = self.dstAddr_z3()
        self.srcAddr = self.srcAddr_z3()
        self.etherType = self.etherType_z3()
        self.valid = Const('ethernet_t_valid', BoolSort())

    def dstAddr_z3(self):
        return ethernet_t.dstAddr(self.const)

    def srcAddr_z3(self):
        return ethernet_t.srcAddr(self.const)

    def etherType_z3(self):
        return ethernet_t.etherType(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", ethernet_t)
        self.revisions.append(self.const)

    def make(self):
        return ethernet_t.mk_ethernet_t(self.dstAddr, self.srcAddr, self.etherType)

    def set(self, lvalue, rvalue):
        z3_copy = self.make()
        update = substitute(z3_copy, (lvalue, rvalue))
        self.update()
        return update

    def isValid(self):
        return self.valid

    def setValid(self):
        self.valid == Var(True, BoolSort())


headers = Datatype("headers")
headers.declare(f"mk_headers", ('ethernet', ethernet_t))
headers = headers.create()


class HEADERS():

    def __init__(self):
        self.name = "headers%s" % str(id(self))[-4:]
        self.ethernet = ETHERNET_T()
        self.const = Const(f"{self.name}_0", headers)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", headers)
        self.revisions.append(self.const)

    def make(self):
        return headers.mk_headers(self.ethernet.make())

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
ma_mac_da_0 = Datatype('ma_mac_da_0')
ma_mac_da_0.declare('mk_ma_mac_da_0', ('key_0', BitVecSort(48)),
                    ('action', IntSort()))
ma_mac_da_0 = ma_mac_da_0.create()


standard_metadata_t = Datatype("standard_metadata_t")
standard_metadata_t.declare(f"mk_standard_metadata_t",
                            # ('ingress_port', BitVecSort(9)),
                            ('egress_spec', BitVecSort(9)),
                            # ('egress_port', BitVecSort(9)),
                            # ('clone_spec', BitVecSort(32)),
                            # ('instance_type', BitVecSort(32)),
                            # ('drop', BitVecSort(1)),
                            # ('recirculate_port', BitVecSort(16)),
                            # ('packet_length', BitVecSort(32)),
                            # ('enq_timestamp', BitVecSort(32)),
                            # ('enq_qdepth', BitVecSort(19)),
                            # ('deq_timedelta', BitVecSort(32)),
                            # ('deq_qdepth', BitVecSort(19)),
                            # ('ingress_global_timestamp', BitVecSort(48)),
                            # ('egress_global_timestamp', BitVecSort(48)),
                            # ('lf_field_list', BitVecSort(32)),
                            # ('mcast_grp', BitVecSort(16)),
                            # ('resubmit_flag', BitVecSort(32)),
                            # ('egress_rid', BitVecSort(16)),
                            # ('recirculate_flag', BitVecSort(32)),
                            # ('checksum_error', BitVecSort(1)),
                            # ('priority', BitVecSort(3)),
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
        # self.ingress_port = self.ingress_port_z3()
        self.egress_spec = self.egress_spec_z3()
        # self.egress_port = self.egress_port_z3()
        # self.clone_spec = self.clone_spec_z3()
        # self.instance_type = self.instance_type_z3()
        # self.drop = self.drop_z3()
        # self.recirculate_port = self.recirculate_port_z3()
        # self.packet_length = self.packet_length_z3()
        # self.enq_timestamp = self.enq_timestamp_z3()
        # self.enq_qdepth = self.enq_qdepth_z3()
        # self.deq_timedelta = self.deq_timedelta_z3()
        # self.deq_qdepth = self.deq_qdepth_z3()
        # self.ingress_global_timestamp = self.ingress_global_timestamp_z3()
        # self.egress_global_timestamp = self.egress_global_timestamp_z3()
        # self.lf_field_list = self.lf_field_list_z3()
        # self.mcast_grp = self.mcast_grp_z3()
        # self.resubmit_flag = self.resubmit_flag_z3()
        # self.egress_rid = self.egress_rid_z3()
        # self.recirculate_flag = self.recirculate_flag_z3()
        # self.checksum_error = self.checksum_error_z3()
        # self.priority = self.priority_z3()

    def ingress_port_z3(self):
        return standard_metadata_t.ingress_port(self.const)

    def egress_spec_z3(self):
        return standard_metadata_t.egress_spec(self.const)

    def egress_port_z3(self):
        return standard_metadata_t.egress_port(self.const)

    def clone_spec_z3(self):
        return standard_metadata_t.clone_spec(self.const)

    def instance_type_z3(self):
        return standard_metadata_t.instance_type(self.const)

    def drop_z3(self):
        return standard_metadata_t.drop(self.const)

    def recirculate_port_z3(self):
        return standard_metadata_t.recirculate_port(self.const)

    def packet_length_z3(self):
        return standard_metadata_t.packet_length(self.const)

    def enq_timestamp_z3(self):
        return standard_metadata_t.enq_timestamp(self.const)

    def enq_qdepth_z3(self):
        return standard_metadata_t.enq_qdepth(self.const)

    def deq_timedelta_z3(self):
        return standard_metadata_t.deq_timedelta(self.const)

    def deq_qdepth_z3(self):
        return standard_metadata_t.deq_qdepth(self.const)

    def ingress_global_timestamp_z3(self):
        return standard_metadata_t.ingress_global_timestamp(self.const)

    def egress_global_timestamp_z3(self):
        return standard_metadata_t.egress_global_timestamp(self.const)

    def lf_field_list_z3(self):
        return standard_metadata_t.lf_field_list(self.const)

    def mcast_grp_z3(self):
        return standard_metadata_t.mcast_grp(self.const)

    def resubmit_flag_z3(self):
        return standard_metadata_t.resubmit_flag(self.const)

    def egress_rid_z3(self):
        return standard_metadata_t.egress_rid(self.const)

    def recirculate_flag_z3(self):
        return standard_metadata_t.recirculate_flag(self.const)

    def checksum_error_z3(self):
        return standard_metadata_t.checksum_error(self.const)

    def priority_z3(self):
        return standard_metadata_t.priority(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", standard_metadata_t)
        self.revisions.append(self.const)

    def make(self):
        return standard_metadata_t.mk_standard_metadata_t(
            # self.ingress_port,
            self.egress_spec,
            # self.egress_port,
            # self.clone_spec,
            # self.instance_type,
            # self.drop,
            # self.recirculate_port,
            # self.packet_length,
            # self.enq_timestamp,
            # self.enq_qdepth,
            # self.deq_timedelta,
            # self.deq_qdepth,
            # self.ingress_global_timestamp,
            # self.egress_global_timestamp,
            # self.lf_field_list,
            # self.mcast_grp,
            # self.resubmit_flag,
            # self.egress_rid,
            # self.recirculate_flag,
            # self.checksum_error,
            # self.priority,
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
               ('standard_metadata', standard_metadata_t))
inouts = inouts.create()


class INOUTS():

    def __init__(self):
        self.name = "inouts%s" % str(id(self))[-4:]
        self.hdr = HEADERS()
        self.meta = META()
        self.standard_metadata = STANDARD_METADATA_T()
        self.const = Const(f"{self.name}_0", inouts)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", inouts)
        self.revisions.append(self.const)

    def make(self):
        return inouts.mk_inouts(self.hdr.make(),
                                self.meta.make(),
                                self.standard_metadata.make())

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


''' INPUT CONTROL '''
# The possible table entries
mac_da_0_m = Const('ma_mac_da_0_m', ma_mac_da_0)
# Reduce the range of action outputs to the total number of actions
# In this case we only have 2 actions
s.add(0 < ma_mac_da_0.action(mac_da_0_m), ma_mac_da_0.action(mac_da_0_m) < 3)


def z3_check():

    inouts = INOUTS()
    bounds = [inouts.const, mac_da_0_m]
    print(control_ingress_1(inouts))
    exit(0)
    tv_equiv = simplify(control_ingress_2(inouts) != control_ingress_3(inouts))
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


def step(func_chain, inouts, expr=True):

    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        # emulate pass-by-value behavior
        inouts = copy.deepcopy(inouts)
        expr = next_fun(func_chain, inouts)
    return expr


def z3_call(fun, inouts, *args):
    inouts = copy.deepcopy(inouts)
    return fun(func_chain, inouts, *args)


def mark_to_drop(assigns, standard_metadata):
    assigns = []

    rval = BitVecVal(0, 1)
    standard_metadata.drop = rval
    update = standard_metadata.set(inouts.standard_metadata.drop, rval)
    assigns.append(inouts.const == update)

    rval = BitVecVal(0, 16)
    inouts.standard_metadata.mcast_grp = rval
    update = standard_metadata.set(inouts.standard_metadata.mcast_grp, rval)
    assigns.append(inouts.const == update)

    return assigns


def control_ingress_0(inouts):

    def my_drop(func_chain, inouts, smeta):
        assigns = []
        expr = And(assigns)

        return step(func_chain, inouts)

    tmp = BitVec("tmp", 16)

    def set_port(func_chain, inouts, output_port):
        assigns = []

        rval = output_port
        inouts.standard_metadata.egress_spec = rval
        update = inouts.set(inouts.standard_metadata.egress_spec, rval)
        assigns.append(inouts.const == update)

        expr = And(assigns)
        return step(func_chain, inouts)

    def mac_da_0(func_chain, inouts):

        def actions():
            actions = []
            output_port = BitVec("output_port", 9)
            actions.append(
                Implies(ma_mac_da_0.action(mac_da_0_m) == 1,
                        set_port(func_chain, inouts, output_port)))
            actions.append(False)
            return Xor(*actions)

        key_matches = []
        mac_da_0_key_0 = inouts.hdr.ethernet.dstAddr
        key_matches.append(mac_da_0_key_0 == ma_mac_da_0.key_0(mac_da_0_m))

        def default():
            return my_drop(func_chain, inouts, inouts.standard_metadata)

        expr = If(And(key_matches), actions(), default())
        return step(func_chain, inouts)

    def apply(func_chain, inouts):
        assigns = []
        assigns.append(mac_da_0)

        def block(func_chain, inouts):
            assigns = []

            x_0 = Extract(15, 0, inouts.hdr.ethernet.srcAddr)
            hasReturned = Var(False, BoolSort())
            retval = BitVec("retval", 16)

            def if_block(func_chain, inouts):

                condition = (x_0 > BitVecVal(5, 16))

                def is_true():
                    assigns = []

                    def local_update(func_chain, inouts):
                        assigns = []

                        nonlocal hasReturned
                        hasReturned = Var(True, BoolSort())
                        expr = And(assigns)
                        return step(func_chain, inouts)
                    assigns.append(local_update)

                    def local_update(func_chain, inouts):
                        assigns = []

                        nonlocal retval
                        retval = x_0 + BitVecVal(65535, 16)
                        expr = And(assigns)
                        return step(func_chain, inouts)
                    assigns.append(local_update)
                    expr = And(assigns)
                    return step(func_chain, inouts)

                def is_false():
                    assigns = []

                    def local_update(func_chain, inouts):
                        assigns = []

                        nonlocal hasReturned
                        hasReturned = Var(True, BoolSort())
                        expr = And(assigns)
                        return step(func_chain, inouts)
                    assigns.append(local_update)

                    def local_update(func_chain, inouts):
                        assigns = []

                        nonlocal retval
                        retval = x_0
                        expr = And(assigns)
                        return step(func_chain, inouts)
                    assigns.append(local_update)
                    expr = And(assigns)
                    return step(func_chain, inouts)

                return If(condition, is_true(),
                          is_false())
            assigns.append(if_block(func_chain, inouts))

            def local_update(func_chain, inouts):
                assigns = []

                nonlocal tmp
                tmp = retval
                expr = And(assigns)
                return step(func_chain, inouts)
            assigns.append(local_update)
            expr = And(assigns)
            return step(func_chain, inouts)
        assigns.append(z3_call(block, inouts))

        def output_update(func_chain, inouts):
            assigns = []

            rval = Concat(Extract(47, 16, inouts.hdr.ethernet.srcAddr), tmp)
            inouts.hdr.ethernet.srcAddr = rval
            update = inouts.set(inouts.hdr.ethernet.srcAddr, rval)
            assigns.append(inouts.const == update)
            expr = And(assigns)
            return step(func_chain, inouts)
        assigns.append(output_update)

        expr = And(assigns)
        return step(func_chain, inouts)
    return apply(func_chain, inouts)


def control_ingress_1(inouts):

    retval = BitVec("retval", 16)

    def my_drop(func_chain, inouts, smeta):
        assigns = []

        expr = And(assigns)
        return step(func_chain, inouts)

    tmp = BitVec("tmp", 16)

    def set_port(func_chain, inouts, output_port):
        assigns = []

        rval = output_port
        inouts.standard_metadata.egress_spec = rval
        update = inouts.set(inouts.standard_metadata.egress_spec, rval)
        assigns.append(inouts.const == update)

        expr = And(assigns)
        return step(func_chain, inouts)

    def mac_da_0(func_chain, inouts):

        def actions():
            actions = []
            output_port = BitVec("output_port", 9)
            actions.append(
                Implies(ma_mac_da_0.action(mac_da_0_m) == 1,
                        set_port(func_chain, inouts, output_port)))
            actions.append(False)
            return Xor(*actions)

        key_matches = []
        mac_da_0_key_0 = inouts.hdr.ethernet.dstAddr
        key_matches.append(mac_da_0_key_0 == ma_mac_da_0.key_0(mac_da_0_m))

        def default():
            return my_drop(func_chain, inouts, inouts.standard_metadata)

        return If(And(key_matches), actions(), default())

    def apply(func_chain, inouts):
        sub_chain = []

        sub_chain.append(mac_da_0)

        def block(func_chain, inouts):
            sub_chain = []

            def if_block(func_chain, inouts):

                condition = (
                    Extract(15, 0, inouts.hdr.ethernet.srcAddr) > BitVecVal(5, 16))

                def is_true():
                    sub_chain = []

                    def local_update(func_chain, inouts):

                        nonlocal retval
                        retval = (Extract(15, 0, inouts.hdr.ethernet.srcAddr) +
                                  BitVecVal(65535, 16))
                        return step(func_chain, inouts)
                    sub_chain.append(local_update)

                    sub_chain.extend(func_chain)
                    return step(sub_chain, inouts)

                def is_false():
                    sub_chain = []

                    def local_update(func_chain, inouts):

                        nonlocal retval
                        retval = Extract(15, 0, inouts.hdr.ethernet.srcAddr)
                        return step(func_chain, inouts)
                    sub_chain.append(local_update)

                    sub_chain.extend(func_chain)
                    return step(sub_chain, inouts)
                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            sub_chain.extend(func_chain)
            return step(sub_chain, inouts)
        sub_chain.append(block)

        def output_update(func_chain, inouts):

            rval = Concat(Extract(47, 16, inouts.hdr.ethernet.srcAddr), retval)
            inouts.hdr.ethernet.srcAddr = rval
            update = inouts.set(inouts.hdr.ethernet.srcAddr, rval)
            expr = (inouts.const == update)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        def output_update(func_chain, inouts):

            rval = Concat(Extract(45, 14, inouts.hdr.ethernet.dstAddr), retval)
            inouts.hdr.ethernet.dstAddr = rval
            update = inouts.set(inouts.hdr.ethernet.dstAddr, rval)
            expr = (inouts.const == update)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    return step(func_chain=[apply], inouts=inouts)


if __name__ == '__main__':
    z3_check()
