from z3 import *

''' Standard metadata definitions. These are typically defined by the model
    imported on top of the file.'''

standard_metadata_t = Datatype("standard_metadata_t")
standard_metadata_t.declare("mk_standard_metadata_t",
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

    # def ingress_port_z3(self):
    #     return standard_metadata_t.ingress_port(self.const)

    def egress_spec_z3(self):
        return standard_metadata_t.egress_spec(self.const)

    # def egress_port_z3(self):
    #     return standard_metadata_t.egress_port(self.const)

    # def clone_spec_z3(self):
    #     return standard_metadata_t.clone_spec(self.const)

    # def instance_type_z3(self):
    #     return standard_metadata_t.instance_type(self.const)

    # def drop_z3(self):
    #     return standard_metadata_t.drop(self.const)

    # def recirculate_port_z3(self):
    #     return standard_metadata_t.recirculate_port(self.const)

    # def packet_length_z3(self):
    #     return standard_metadata_t.packet_length(self.const)

    # def enq_timestamp_z3(self):
    #     return standard_metadata_t.enq_timestamp(self.const)

    # def enq_qdepth_z3(self):
    #     return standard_metadata_t.enq_qdepth(self.const)

    # def deq_timedelta_z3(self):
    #     return standard_metadata_t.deq_timedelta(self.const)

    # def deq_qdepth_z3(self):
    #     return standard_metadata_t.deq_qdepth(self.const)

    # def ingress_global_timestamp_z3(self):
    #     return standard_metadata_t.ingress_global_timestamp(self.const)

    # def egress_global_timestamp_z3(self):
    #     return standard_metadata_t.egress_global_timestamp(self.const)

    # def lf_field_list_z3(self):
    #     return standard_metadata_t.lf_field_list(self.const)

    # def mcast_grp_z3(self):
    #     return standard_metadata_t.mcast_grp(self.const)

    # def resubmit_flag_z3(self):
    #     return standard_metadata_t.resubmit_flag(self.const)

    # def egress_rid_z3(self):
    #     return standard_metadata_t.egress_rid(self.const)

    # def recirculate_flag_z3(self):
    #     return standard_metadata_t.recirculate_flag(self.const)

    # def checksum_error_z3(self):
    #     return standard_metadata_t.checksum_error(self.const)

    # def priority_z3(self):
    #     return standard_metadata_t.priority(self.const)

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


def mark_to_drop(func_chain, inouts, assigns, standard_metadata):
    assigns = []

    rval = BitVecVal(0, 1)
    standard_metadata.drop = rval
    update = standard_metadata.set(inouts.standard_metadata.drop, rval)
    assigns.append(inouts.const == update)

    rval = BitVecVal(0, 16)
    inouts.standard_metadata.mcast_grp = rval
    update = standard_metadata.set(inouts.standard_metadata.mcast_grp, rval)
    assigns.append(inouts.const == update)
    expr = And(assigns)
    return step(func_chain, inouts, expr)
