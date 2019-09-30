from p4z3.expressions import *

''' Standard metadata definitions. These are typically defined by the model
    imported on top of the file.'''


def register(z3_reg):
    z3_args = [('ingress_port', BitVecSort(9)),
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
               ]
    z3_reg.register_z3_type("standard_metadata_t", Struct, z3_args)

    mark_to_drop = P4Action()
    mark_to_drop.add_parameter("smeta", z3_reg.types["standard_metadata_t"])

    def BLOCK():
        block = BlockStatement()
        lval = "smeta.drop"
        rval = BitVecVal(1, 1)
        stmt = AssignmentStatement(lval, rval)
        block.add(stmt)
        lval = "smeta.mcast_grp"
        rval = BitVecVal(0, 16)
        stmt = AssignmentStatement(lval, rval)
        block.add(stmt)

        return block
    stmt = BLOCK()
    mark_to_drop.add_stmt(stmt)
    z3_reg.register_extern("mark_to_drop", mark_to_drop)
    return z3_reg
