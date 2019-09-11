from p4z3_expressions import *


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = []
    z3_reg.register_z3_type("metadata", Struct, z3_args)

    def p():
        pass

    def vrfy():
        pass

    def update():
        pass

    def egress():
        pass

    def deparser():
        pass

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["metadata"]),
               ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):

        def my_drop(p4_vars, expr_chain, smeta):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def set_port(p4_vars, expr_chain, output_port):
            def BLOCK():
                block = BlockStatement()
                lval = "standard_metadata.egress_spec"
                rval = output_port
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        mac_da_0 = TableExpr("mac_da_0")

        args = [BitVec("mac_da_0_output_port", 9)]
        mac_da_0.add_action("set_port", set_port, args)

        args = ["standard_metadata.const"]
        mac_da_0.add_action("my_drop", my_drop, args)

        args = ["standard_metadata.const"]
        mac_da_0.add_default(my_drop, args)

        table_key = "hdr.ethernet.dstAddr"
        mac_da_0.add_match(table_key)

        def BLOCK():
            block = BlockStatement()
            block.add(mac_da_0.apply())

            def BLOCK():
                block = BlockStatement()

                rval = P4Slice("hdr.ethernet.srcAddr", 15, 0)
                lval = "x_0"
                assign = AssignmentStatement(lval, rval)
                block.add(assign)

                rval = False
                lval = "hasReturned"
                assign = AssignmentStatement(lval, rval)
                block.add(assign)

                rval = BitVec("retval", 16)
                lval = "retval"
                assign = AssignmentStatement(lval, rval)
                block.add(assign)

                if_block = IfStatement()

                condition = P4gt("x_0", BitVecVal(5, 16))
                if_block.add_condition(condition)

                rval = True
                lval = "hasReturned"
                assign = AssignmentStatement(lval, rval)
                if_block.add_then_stmt(assign)

                rval = P4add("x_0", BitVecVal(65535, 16))
                lval = "retval"
                assign = AssignmentStatement(lval, rval)
                if_block.add_then_stmt(assign)

                rval = True
                lval = "hasReturned"
                assign = AssignmentStatement(lval, rval)
                if_block.add_else_stmt(assign)

                rval = "x_0"
                lval = "retval"
                assign = AssignmentStatement(lval, rval)
                if_block.add_else_stmt(assign)
                block.add(if_block)

                rval = "retval"
                lval = "tmp"
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            block.add(BLOCK())

            rval = "tmp"
            lval = "hdr.ethernet.srcAddr"
            assign = SliceAssignment(
                lval, rval, 15, 0)
            block.add(assign)
            return block

        return BLOCK().eval(p4_vars)

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = []
    z3_reg.register_z3_type("metadata", Struct, z3_args)

    def p():
        pass

    def vrfy():
        pass

    def update():
        pass

    def egress():
        pass

    def deparser():
        pass

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["metadata"]),
               ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):

        def my_drop(p4_vars, expr_chain, smeta):
            def BLOCK():
                block = BlockStatement()
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def set_port(p4_vars, expr_chain, output_port):
            def BLOCK():
                block = BlockStatement()
                lval = "standard_metadata.egress_spec"
                rval = output_port
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        mac_da_0 = TableExpr("mac_da_0")

        args = [BitVec("mac_da_0_output_port", 9)]
        mac_da_0.add_action("set_port", set_port, args)

        args = ["standard_metadata.const"]
        mac_da_0.add_action("my_drop", my_drop, args)

        args = ["standard_metadata.const"]
        mac_da_0.add_default(my_drop, args)

        table_key = "hdr.ethernet.dstAddr"
        mac_da_0.add_match(table_key)

        def BLOCK():
            block = BlockStatement()
            block.add(mac_da_0.apply())

            if_block = IfStatement()

            condition = P4gt(P4Slice("hdr.ethernet.srcAddr", 15, 0),
                             BitVecVal(5, 16))
            if_block.add_condition(condition)

            rval = P4add(P4Slice("hdr.ethernet.srcAddr", 15, 0),
                         BitVecVal(65535, 16))
            lval = "retval"
            assign = AssignmentStatement(lval, rval)
            if_block.add_then_stmt(assign)

            rval = P4Slice("hdr.ethernet.srcAddr", 15, 0)
            lval = "retval"
            assign = AssignmentStatement(lval, rval)
            if_block.add_else_stmt(assign)

            block.add(if_block)

            rval = P4or(P4and("hdr.ethernet.srcAddr", P4inv(BitVecVal(
                0xffff, 48))), P4and(P4rshift(P4Cast("retval", 48), 0), BitVecVal(0xffff, 48)))
            lval = "hdr.ethernet.srcAddr"
            assign = AssignmentStatement(lval, rval)
            block.add(assign)
            return block

        return BLOCK().eval(p4_vars)

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def z3_check():
    s = Solver()

    p4_ctrl_0, p4_ctrl_0_args = p4_program_0(Z3Reg())[2]
    p4_ctrl_1, p4_ctrl_1_args = p4_program_1(Z3Reg())[2]

    print("PROGRAM 1")
    print(p4_ctrl_0(p4_ctrl_0_args))
    print("PROGRAM 2")
    print(p4_ctrl_1(p4_ctrl_1_args))
    tv_equiv = simplify(p4_ctrl_0(p4_ctrl_0_args) !=
                        p4_ctrl_1(p4_ctrl_1_args))
    s.add(tv_equiv)
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
