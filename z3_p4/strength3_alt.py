from p4z3_expressions import *


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [('a', BitVecSort(16)), ('b', BitVecSort(16)),
               ('c', BitVecSort(8))]
    z3_reg.register_z3_type("hdr", Header, z3_args)

    z3_args = [('h', z3_reg.types["hdr"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('x', BitVecSort(16)), ('y', BitVecSort(16))]
    z3_reg.register_z3_type("meta", Struct, z3_args)

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

    z3_args = [('h', z3_reg.types["headers"]), ('m', z3_reg.types["meta"]),
               ('sm', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):

        def case0(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Concat(P4Slice(P4Concat(
                    BitVecVal(0, 16), p4_vars.h.h.a), 15, 0), BitVecVal(0, 16)), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case1(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Slice(p4_vars.h.h.a, 15, 0), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case2(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = BitVecVal(0, 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case3(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Slice(p4_vars.h.h.a, 7, 0)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case4(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Concat(BitVecVal(0, 8),
                                       P4Slice(p4_vars.h.h.a, 15, 0)), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case5(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Concat(BitVecVal(0, 8),
                                       P4Slice(p4_vars.h.h.a, 15, 8)), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case6(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Concat(BitVecVal(0, 16),
                                       P4Slice(p4_vars.h.h.a, 15, 8)), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case7(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Slice(P4rshift(P4Concat(BitVecVal(0, 16),
                                                        p4_vars.h.h.a), 3), 31, 8), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        t_0 = TableExpr("t_0")
        t_0.add_action("case0", case0)
        t_0.add_action("case1", case1)
        t_0.add_action("case2", case2)
        t_0.add_action("case3", case3)
        t_0.add_action("case4", case4)
        t_0.add_action("case5", case5)
        t_0.add_action("case6", case6)
        t_0.add_action("case7", case7)
        t_0.add_default(case0)

        def BLOCK():
            block = BlockStatement()

            block.add(t_0.apply())

            return block

        return BLOCK().eval(p4_vars)

        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):
    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [('a', BitVecSort(16)), ('b', BitVecSort(16)),
               ('c', BitVecSort(8))]
    z3_reg.register_z3_type("hdr", Header, z3_args)

    z3_args = [('h', z3_reg.types["hdr"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('x', BitVecSort(16)), ('y', BitVecSort(16))]
    z3_reg.register_z3_type("meta", Struct, z3_args)

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

    z3_args = [('h', z3_reg.types["headers"]), ('m', z3_reg.types["meta"]),
               ('sm', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):

        def case0(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(
                    P4Concat(P4Slice("h.h.a", 15, 0), BitVecVal(0, 16)), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case1(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Slice(p4_vars.h.h.a, 15, 0), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case2(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = BitVecVal(0, 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case3(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Slice(p4_vars.h.h.a, 7, 0)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case4(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Concat(BitVecVal(0, 8),
                                       P4Slice(p4_vars.h.h.a, 15, 0)), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case5(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Concat(BitVecVal(0, 8),
                                       P4Slice(p4_vars.h.h.a, 15, 8)), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case6(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Concat(BitVecVal(0, 16),
                                       P4Slice(p4_vars.h.h.a, 15, 8)), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        def case7(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.c"
                rval = P4Cast(P4Slice(P4rshift(P4Concat(BitVecVal(0, 16),
                                                        p4_vars.h.h.a), 3), 31, 8), 8)
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        t_0 = TableExpr("t_0")
        t_0.add_action("case0", case0)
        t_0.add_action("case1", case1)
        t_0.add_action("case2", case2)
        t_0.add_action("case3", case3)
        t_0.add_action("case4", case4)
        t_0.add_action("case5", case5)
        t_0.add_action("case6", case6)
        t_0.add_action("case7", case7)
        t_0.add_default(case0)

        def BLOCK():
            block = BlockStatement()

            block.add(t_0.apply())

            return block

        return BLOCK().eval(p4_vars)

        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def z3_check():
    ''' SOLVER '''
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
