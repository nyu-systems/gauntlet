from p4z3_expressions import *


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
    ]
    z3_reg.register_z3_type("Meta", Struct, z3_args)

    z3_args = [
        ('a', BitVecSort(32)),
        ('b', BitVecSort(32))]
    z3_reg.register_z3_type("hdr", Header, z3_args)

    z3_args = [
        ('h', z3_reg.types["hdr"])]
    z3_reg.register_z3_type("Headers", Struct, z3_args)

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
        ('h', z3_reg.types["Headers"]),
        ('m', z3_reg.types["Meta"]),
        ('sm', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)

    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        NoAction_0 = P4Action()

        def BLOCK():
            block = BlockStatement()

            return block

        stmt = BLOCK()

        NoAction_0.add_stmt(stmt)

        p4_vars.set_or_add_var("NoAction_0", NoAction_0)

        c_a_0 = P4Action()

        def BLOCK():
            block = BlockStatement()
            lval = "h.h.b"
            rval = "h.h.a"
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            return block

        stmt = BLOCK()

        c_a_0.add_stmt(stmt)

        p4_vars.set_or_add_var("c_a_0", c_a_0)

        c_t = P4Table("c_t")
        table_key = P4add("h.h.a", "h.h.a")
        c_t.add_match(table_key)

        c_t.add_action(p4_vars, MethodCallExpr("c_a_0"))
        c_t.add_action(p4_vars, MethodCallExpr("NoAction_0"))

        c_t.add_default(p4_vars, MethodCallExpr("NoAction_0"))

        p4_vars.set_or_add_var("c_t", c_t)

        def BLOCK():
            block = BlockStatement()
            stmt = MethodCallStmt(MethodCallExpr("c_t.apply"))
            block.add(stmt)
            lval = "sm.egress_spec"
            rval = BitVecVal(0, 9)
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            return block

        stmt = BLOCK()

        return stmt.eval(p4_vars)

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):
    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
    ]
    z3_reg.register_z3_type("Meta", Struct, z3_args)

    z3_args = [
        ('a', BitVecSort(32)),
        ('b', BitVecSort(32))]
    z3_reg.register_z3_type("hdr", Header, z3_args)

    z3_args = [
        ('h', z3_reg.types["hdr"])]
    z3_reg.register_z3_type("Headers", Struct, z3_args)

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
        ('h', z3_reg.types["Headers"]),
        ('m', z3_reg.types["Meta"]),
        ('sm', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)

    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        NoAction_0 = P4Action()

        def BLOCK():
            block = BlockStatement()

            return block

        stmt = BLOCK()

        NoAction_0.add_stmt(stmt)

        p4_vars.set_or_add_var("NoAction_0", NoAction_0)

        c_a_0 = P4Action()

        def BLOCK():
            block = BlockStatement()
            lval = "h.h.b"
            rval = "h.h.a"
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            return block

        stmt = BLOCK()

        c_a_0.add_stmt(stmt)

        p4_vars.set_or_add_var("c_a_0", c_a_0)

        c_t = P4Table("c_t")
        table_key = P4add("h.h.a", "h.h.a")
        c_t.add_match(table_key)

        c_t.add_action(p4_vars, MethodCallExpr("c_a_0"))
        c_t.add_action(p4_vars, MethodCallExpr("NoAction_0"))

        c_t.add_default(p4_vars, MethodCallExpr("NoAction_0"))

        p4_vars.set_or_add_var("c_t", c_t)

        def BLOCK():
            block = BlockStatement()
            stmt = MethodCallStmt(MethodCallExpr("c_t.apply"))
            block.add(stmt)
            lval = "sm.egress_spec"
            rval = BitVecVal(0, 9)
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            return block

        stmt = BLOCK()

        return stmt.eval(p4_vars)

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    s = Solver()

    # bounds = [p4_vars.const]
    # out = control_ingress_1(s, p4_vars)
    # print("FINAL OUTPUT")
    # print(out)
    # exit(0)
    # the equivalence equation
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
