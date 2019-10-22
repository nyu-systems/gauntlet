from p4z3.expressions import *

''' Standard metadata definitions. These are typically defined by the model
    imported on top of the file.'''


def register(z3_reg):
    z3_reg.register_typedef("error", z3.BitVecSort(1))
    z3_args = [('ingress_port', z3.BitVecSort(9)),
               ('egress_spec', z3.BitVecSort(9)),
               ('egress_port', z3.BitVecSort(9)),
               ('instance_type', z3.BitVecSort(32)),
               ('packet_length', z3.BitVecSort(32)),
               ('enq_timestamp', z3.BitVecSort(32)),
               ('enq_qdepth', z3.BitVecSort(19)),
               ('deq_timedelta', z3.BitVecSort(32)),
               ('deq_qdepth', z3.BitVecSort(19)),
               ('ingress_global_timestamp', z3.BitVecSort(48)),
               ('egress_global_timestamp', z3.BitVecSort(48)),
               ('mcast_grp', z3.BitVecSort(16)),
               ('egress_rid', z3.BitVecSort(16)),
               ('checksum_error', z3.BitVecSort(1)),
               ('parser_error', z3.BitVecSort(1)),
               ('priority', z3.BitVecSort(3)),
               ]
    z3_reg.register_struct("standard_metadata_t", z3_args)

    mark_to_drop = P4Action()
    mark_to_drop.add_parameter("smeta", z3_reg.type("standard_metadata_t"))

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
