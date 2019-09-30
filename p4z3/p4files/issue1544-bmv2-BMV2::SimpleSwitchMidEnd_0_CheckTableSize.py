from p4z3_expressions import *


def p4_program(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]
    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [
        ('ethernet', z3_reg.types["ethernet_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [
    ]
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

    z3_args = [
        ('hdr', z3_reg.types["headers"]),
        ('meta', z3_reg.types["metadata"]),
        ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)

    ingress_args = z3_reg.instance("inouts")
    ingress_args.add_externs(z3_reg.externs)

    def ingress(p4_vars):
        my_drop = P4Action()
        my_drop.add_parameter("smeta", z3_reg.types["standard_metadata_t"])

        def BLOCK():
            block = BlockStatement()
            stmt = MethodCallStmt(MethodCallExpr("mark_to_drop", "smeta"))
            block.add(stmt)

            return block

        stmt = BLOCK()

        my_drop.add_stmt(stmt)

        p4_vars.set_or_add_var("my_drop", my_drop)

        set_port = P4Action()
        set_port.add_parameter("output_port", BitVecSort(9))

        def BLOCK():
            block = BlockStatement()
            lval = "standard_metadata.egress_spec"
            rval = "output_port"
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            return block

        stmt = BLOCK()

        set_port.add_stmt(stmt)

        p4_vars.set_or_add_var("set_port", set_port)

        mac_da_0 = P4Table("mac_da_0")
        table_key = "hdr.ethernet.dstAddr"
        mac_da_0.add_match(table_key)

        mac_da_0.add_action(p4_vars, MethodCallExpr("set_port"))
        mac_da_0.add_action(p4_vars, MethodCallExpr(
            "my_drop", "standard_metadata"))

        mac_da_0.add_default(p4_vars, MethodCallExpr(
            "my_drop", "standard_metadata"))

        p4_vars.set_or_add_var("mac_da_0", mac_da_0)

        def BLOCK():
            block = BlockStatement()
            stmt = MethodCallStmt(MethodCallExpr("mac_da_0.apply"))
            block.add(stmt)

            def BLOCK():
                block = BlockStatement()
                lval = "x_0"
                rval = P4Slice("hdr.ethernet.srcAddr", 15, 0)
                stmt = P4Declaration(lval, rval)
                block.add(stmt)
                lval = "hasReturned"
                rval = False
                stmt = P4Declaration(lval, rval)
                block.add(stmt)
                lval = "retval"
                stmt = P4Declaration(lval)
                block.add(stmt)
                if_block = IfStatement()

                condition = P4gt("x_0", BitVecVal(5, 16))

                if_block.add_condition(condition)

                def BLOCK():
                    block = BlockStatement()
                    lval = "hasReturned"
                    rval = True
                    stmt = AssignmentStatement(lval, rval)
                    block.add(stmt)
                    lval = "retval"
                    rval = P4add("x_0", BitVecVal(65535, 16))
                    stmt = AssignmentStatement(lval, rval)
                    block.add(stmt)

                    return block

                stmt = BLOCK()

                if_block.add_then_stmt(stmt)

                def BLOCK():
                    block = BlockStatement()
                    lval = "hasReturned"
                    rval = True
                    stmt = AssignmentStatement(lval, rval)
                    block.add(stmt)
                    lval = "retval"
                    rval = "x_0"
                    stmt = AssignmentStatement(lval, rval)
                    block.add(stmt)

                    return block

                stmt = BLOCK()

                if_block.add_else_stmt(stmt)

                stmt = if_block
                block.add(stmt)
                lval = "tmp"
                rval = "retval"
                stmt = AssignmentStatement(lval, rval)
                block.add(stmt)

                return block

            stmt = BLOCK()

            block.add(stmt)
            lval = "hdr.ethernet.srcAddr"
            rval = "tmp"
            stmt = SliceAssignment(lval, rval, 15, 0)
            block.add(stmt)

            return block

        stmt = BLOCK()

        return stmt.eval(p4_vars)

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))
