from p4z3_base import *

''' Standard metadata definitions. These are typically defined by the model
    imported on top of the file.'''
z3_args = [('ingress_port', BitVecSort(9)),
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
           ]
z3_reg.register_z3_type("standard_metadata_t", Struct, z3_args)


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
