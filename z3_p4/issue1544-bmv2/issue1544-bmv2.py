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
                            ('ingress_port', BitVecSort(9)),
                            ('egress_spec', BitVecSort(9)),
                            ('egress_port', BitVecSort(9)),
                            ('clone_spec', BitVecSort(32)),
                            ('instance_type', BitVecSort(32)),
                            ('drop', BitVecSort(1)),
                            ('recirculate_port', BitVecSort(16)),
                            ('packet_length', BitVecSort(32)),
                            ('enq_timestamp', BitVecSort(32)),
                            ('enq_qdepth', BitVecSort(19)),
                            ('deq_timedelta', BitVecSort(32)),
                            ('deq_qdepth', BitVecSort(19)),
                            ('ingress_global_timestamp', BitVecSort(48)),
                            ('egress_global_timestamp', BitVecSort(48)),
                            ('lf_field_list', BitVecSort(32)),
                            ('mcast_grp', BitVecSort(16)),
                            ('resubmit_flag', BitVecSort(32)),
                            ('egress_rid', BitVecSort(16)),
                            ('recirculate_flag', BitVecSort(32)),
                            ('checksum_error', BitVecSort(1)),
                            ('priority', BitVecSort(3)),
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
        self.ingress_port = self.ingress_port_z3()
        self.egress_spec = self.egress_spec_z3()
        self.egress_port = self.egress_port_z3()
        self.clone_spec = self.clone_spec_z3()
        self.instance_type = self.instance_type_z3()
        self.drop = self.drop_z3()
        self.recirculate_port = self.recirculate_port_z3()
        self.packet_length = self.packet_length_z3()
        self.enq_timestamp = self.enq_timestamp_z3()
        self.enq_qdepth = self.enq_qdepth_z3()
        self.deq_timedelta = self.deq_timedelta_z3()
        self.deq_qdepth = self.deq_qdepth_z3()
        self.ingress_global_timestamp = self.ingress_global_timestamp_z3()
        self.egress_global_timestamp = self.egress_global_timestamp_z3()
        self.lf_field_list = self.lf_field_list_z3()
        self.mcast_grp = self.mcast_grp_z3()
        self.resubmit_flag = self.resubmit_flag_z3()
        self.egress_rid = self.egress_rid_z3()
        self.recirculate_flag = self.recirculate_flag_z3()
        self.checksum_error = self.checksum_error_z3()
        self.priority = self.priority_z3()

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
            self.ingress_port,
            self.egress_spec,
            self.egress_port,
            self.clone_spec,
            self.instance_type,
            self.drop,
            self.recirculate_port,
            self.packet_length,
            self.enq_timestamp,
            self.enq_qdepth,
            self.deq_timedelta,
            self.deq_qdepth,
            self.ingress_global_timestamp,
            self.egress_global_timestamp,
            self.lf_field_list,
            self.mcast_grp,
            self.resubmit_flag,
            self.egress_rid,
            self.recirculate_flag,
            self.checksum_error,
            self.priority,
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
    bounds = [inouts.const, mac_da_0_m]
    # the equivalence equation
    tv_equiv = simplify(control_ingress_0(inouts) != control_ingress_0(inouts))
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

    # @name(".NoAction") action NoAction_0() {
    # }
    def my_drop(func_chain, inouts, smeta):
        ''' This is an action '''
        assigns = []
        return step(func_chain, inouts, assigns)

    tmp = BitVec("tmp", 16)

    def set_port(func_chain, inouts, output_port):
        ''' This is an action '''
        assigns = []

        rval = output_port
        inouts.standard_metadata.egress_spec = output_port
        inouts.set(inouts.standard_metadata.egress_spec, rval)
        return step(func_chain, inouts, assigns)

    # @name("ingress.c.t") table mac_da_0 {
    def mac_da_0(func_chain, inouts):
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
            output_port = BitVec("output_port", 9)
            actions.append(
                Implies(ma_mac_da_0.action(mac_da_0_m) == 1,
                        set_port(func_chain, inouts, output_port)))
            actions.append(
                Implies(ma_mac_da_0.action(mac_da_0_m) == 2,
                        my_drop(func_chain, inouts, inouts.standard_metadata)))
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        # key = {
        #     h.h.a + h.h.a: exact @name("e") ;
        # }
        key_matches = []
        mac_da_0_key_0 = inouts.hdr.ethernet.dstAddr
        # It is an exact match, so we use direct comparison
        key_matches.append(mac_da_0_key_0 == ma_mac_da_0.key_0(mac_da_0_m))

        # default_action = NoAction_0();
        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return my_drop(func_chain, inouts, inouts.standard_metadata)

        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), actions(), default())

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []
        # mac_da_0.apply();
        func_chain.append(mac_da_0)

        def block(func_chain):
            x_0 = Extract(15, 0, inouts.hdr.ethernet.srcAddr)
            hasReturned = Var(False, BoolSort())
            retval = BitVec("retval", 16)

            def if_block(func_chain, inouts):

                # If blocks track two expression lists for the if and the else case
                # if (hdr.h.s == hdr.a[0].s)
                condition = (x_0 > BitVecVal(5, 16))
                if_list = list(func_chain)
                else_list = list(func_chain)
                assignments = []

                def local_update(func_chain, inouts):
                    assigns = []
                    # key_0 is updated to have the value h.h.a + h.h.a
                    nonlocal hasReturned
                    hasReturned = Var(True, BoolSort())
                    return step(func_chain, inouts, assigns)
                if_list.append(local_update)

                def local_update(func_chain, inouts):
                    assigns = []
                    # key_0 is updated to have the value h.h.a + h.h.a
                    nonlocal retval
                    retval = x_0 + BitVecVal(65535, 16)
                    return step(func_chain, inouts, assigns)
                if_list.append(local_update)

                def local_update(func_chain, inouts):
                    assigns = []
                    # key_0 is updated to have the value h.h.a + h.h.a
                    nonlocal hasReturned
                    hasReturned = Var(True, BoolSort())
                    return step(func_chain, inouts, assigns)
                else_list.append(local_update)

                def local_update(func_chain, inouts):
                    assigns = []
                    # key_0 is updated to have the value h.h.a + h.h.a
                    nonlocal retval
                    retval = x_0
                    return step(func_chain, inouts, assigns)
                else_list.append(local_update)

                return If(condition, step(if_list, inouts, assignments),
                          step(else_list, inouts, assignments))
            func_chain.append(if_block)

            def local_update(func_chain, inouts):
                assigns = []
                nonlocal tmp
                tmp = retval
                return step(func_chain, inouts, assigns)
            func_chain.append(local_update)
            return func_chain
        # }
        func_chain = block(func_chain)

        def output_update(func_chain, inouts):
            assigns = []
            rval = Concat(Extract(47, 16, inouts.hdr.ethernet.srcAddr), tmp)
            inouts.hdr.ethernet.srcAddr = rval
            inouts.set(inouts.hdr.ethernet.srcAddr, rval)
            return step(func_chain, inouts, assigns)

            return step(func_chain, inouts, assigns)
        func_chain.append(output_update)

        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], inouts=inouts)


if __name__ == '__main__':
    z3_check()
