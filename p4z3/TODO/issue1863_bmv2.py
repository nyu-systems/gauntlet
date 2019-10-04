from p4z3.expressions import *
import os


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('dstAddr', z3.BitVecSort(48)),
               ('srcAddr', z3.BitVecSort(48)),
               ('etherType', z3.BitVecSort(16))]
    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('a', z3.BitVecSort(8)),
               ('b', z3.BitVecSort(8))]
    z3_reg.register_z3_type("custom_t", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"]),
               ('custom', z3_reg.types["custom_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('a', z3.BitVecSort(8)),
               ('b', z3.BitVecSort(8))]
    z3_reg.register_z3_type("foo_t", Struct, z3_args)

    z3_args = []
    z3_reg.register_z3_type("metadata_t", Struct, z3_args)

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

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["metadata_t"]),
               ('stdmeta', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")
    ingress_args.add_externs(z3_reg.externs)

    def ingress(p4_vars):
        ctrl_body = BlockStatement()

        lval = "foo_0"
        rval = z3_reg.instance("foo_t")
        stmt = P4Declaration(lval, rval)
        ctrl_body.add(stmt)

        def BLOCK():
            block = BlockStatement()

            lval = "stdmeta.egress_spec"
            rval = z3.BitVecVal(0, 9)
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            lval = "foo_0"
            rval = [z3.BitVecVal(1, 8), z3.BitVecVal(2, 8)]
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            lval = "foo_0"
            rval = P4StructInitializer(z3_reg.instance("foo_t"),
                                       a="foo_0.b",
                                       b="foo_0.a")
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            lval = "hdr.custom.a"
            rval = "foo_0.a"
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            lval = "hdr.custom.b"
            rval = "foo_0.b"
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            return block

        stmt = BLOCK()

        ctrl_body.add(stmt)
        return ctrl_body.eval(p4_vars=p4_vars, expr_chain=[])

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('dstAddr', z3.BitVecSort(48)),
               ('srcAddr', z3.BitVecSort(48)),
               ('etherType', z3.BitVecSort(16))]
    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('a', z3.BitVecSort(8)),
               ('b', z3.BitVecSort(8))]
    z3_reg.register_z3_type("custom_t", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"]),
               ('custom', z3_reg.types["custom_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('a', z3.BitVecSort(8)),
               ('b', z3.BitVecSort(8))]
    z3_reg.register_z3_type("foo_t", Struct, z3_args)

    z3_args = []
    z3_reg.register_z3_type("metadata_t", Struct, z3_args)

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

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["metadata_t"]),
               ('stdmeta', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")
    ingress_args.add_externs(z3_reg.externs)

    def ingress(p4_vars):
        ctrl_body = BlockStatement()

        lval = "foo_0"
        rval = z3_reg.instance("foo_t")
        stmt = P4Declaration(lval, rval)
        ctrl_body.add(stmt)

        def BLOCK():
            block = BlockStatement()

            lval = "stdmeta.egress_spec"
            rval = z3.BitVecVal(0, 9)
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            lval = "foo_0"
            rval = [z3.BitVecVal(1, 8), z3.BitVecVal(2, 8)]
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            lval = "foo_0"
            rval = P4StructInitializer(z3_reg.instance("foo_t"),
                                       a="foo_0.b",
                                       b="foo_0.a")
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            lval = "hdr.custom.a"
            rval = "foo_0.a"
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            lval = "hdr.custom.b"
            rval = "foo_0.b"
            stmt = AssignmentStatement(lval, rval)
            block.add(stmt)

            return block

        stmt = BLOCK()

        ctrl_body.add(stmt)
        return ctrl_body.eval(p4_vars=p4_vars, expr_chain=[])

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def z3_check():
    ''' SOLVER '''
    s = z3.Solver()

    p4_ctrl_0, p4_ctrl_0_args = p4_program_0(Z3Reg())[2]
    p4_ctrl_1, p4_ctrl_1_args = p4_program_1(Z3Reg())[2]

    print("PROGRAM 1")
    print(p4_ctrl_0(p4_ctrl_0_args))
    print("PROGRAM 2")
    print(p4_ctrl_1(p4_ctrl_1_args))
    tv_equiv = z3.simplify(p4_ctrl_0(p4_ctrl_0_args) !=
                           p4_ctrl_1(p4_ctrl_1_args))
    s.add(tv_equiv)
    print(tv_equiv)
    print(s.sexpr())
    ret = s.check()
    if ret == z3.sat:
        print(ret)
        print(s.model())
        return os.EX_PROTOCOL
    else:
        print(ret)
        return os.EX_OK


if __name__ == '__main__':
    z3_check()
