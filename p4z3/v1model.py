from p4z3.expressions import *

''' Standard metadata definitions. These are typically defined by the model
    imported on top of the file.'''


def register(z3_reg):
    z3_args = [('ingress_port', z3.BitVecSort(9)),
               ('egress_spec', z3.BitVecSort(9)),
               ('egress_port', z3.BitVecSort(9)),
               ('clone_spec', z3.BitVecSort(32)),
               ('instance_type', z3.BitVecSort(32)),
               ('drop', z3.BitVecSort(1)),
               ('recirculate_port', z3.BitVecSort(16)),
               ('packet_length', z3.BitVecSort(32)),
               ('enq_timestamp', z3.BitVecSort(32)),
               ('enq_qdepth', z3.BitVecSort(19)),
               ('deq_timedelta', z3.BitVecSort(32)),
               ('deq_qdepth', z3.BitVecSort(19)),
               ('ingress_global_timestamp', z3.BitVecSort(48)),
               ('egress_global_timestamp', z3.BitVecSort(48)),
               ('lf_field_list', z3.BitVecSort(32)),
               ('mcast_grp', z3.BitVecSort(16)),
               ('resubmit_flag', z3.BitVecSort(32)),
               ('egress_rid', z3.BitVecSort(16)),
               ('recirculate_flag', z3.BitVecSort(32)),
               ('parser_error', z3.BitVecSort(1)),
               ('checksum_error', z3.BitVecSort(1)),
               ('priority', z3.BitVecSort(3)),
               ]
    z3_reg.register_z3_type("standard_metadata_t", Struct, z3_args)

    mark_to_drop = P4Action()
    mark_to_drop.add_parameter("smeta", z3_reg.types["standard_metadata_t"])

    def BLOCK():
        block = BlockStatement()
        lval = "smeta.egress_spec"
        rval = z3.BitVecVal(9, 9)
        stmt = AssignmentStatement(lval, rval)
        block.add(stmt)
        lval = "smeta.mcast_grp"
        rval = z3.BitVecVal(0, 16)
        stmt = AssignmentStatement(lval, rval)
        block.add(stmt)

        return block
    stmt = BLOCK()
    mark_to_drop.add_stmt(stmt)
    z3_reg.register_extern("mark_to_drop", mark_to_drop)
    return z3_reg
