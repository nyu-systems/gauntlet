from p4z3_expressions import *


def p4_program_0(z3_reg):
    ''' HEADERS '''
    # The input headers of the control pipeline

    # Model imports at the top of the p4 file '''
    import v1model
    z3_reg = v1model.register(z3_reg)
    # header hdr {
    #     bit<32> a;
    #     bit<32> b;
    # }
    z3_args = [('a', BitVecSort(32)), ('b', BitVecSort(32))]
    z3_reg.register_z3_type("hdr", Header, z3_args)

    ''' STRUCTS '''
    # Data structures that were declared globally

    # struct Headers {
    #     hdr h;
    # }
    z3_args = [('h', z3_reg.types["hdr"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    # struct Meta {
    # }
    z3_args = []
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

    ''' OUTPUT '''
    ''' Initialize the header  These are our inputs and outputs
     Think of it as the header inputs after they have been parsed.
     The final output of the control pipeline in a single data type.
     This corresponds to the arguments of the control function'''

    # control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm)
    z3_args = [('h', z3_reg.types["headers"]), ('m', z3_reg.types["meta"]),
               ('sm', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ''' This is the initial version of the program. '''
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):

        # @name(".NoAction") action NoAction_0() {
        # }
        def NoAction_0(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        # @name("ingress.c.a") action c_a_0() {
        #     h.h.b = h.h.a;
        # }
        def c_a_0(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.b"
                rval = "h.h.a"
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        # @name("ingress.c.t") table c_t {
        c_t = TableExpr("c_t")
        c_t.add_action("c_a_0", c_a_0)
        c_t.add_action("NoAction_0", NoAction_0)
        c_t.add_default(NoAction_0)

        table_key = P4Add("h.h.a", "h.h.a")
        c_t.add_match(table_key)

        def BLOCK():
            block = BlockStatement()

            block.add(c_t.apply())

            rval = BitVecVal(0, 9)
            lval = "sm.egress_spec"
            assign = AssignmentStatement(lval, rval)

            block.add(assign)
            return block

        return BLOCK().eval(p4_vars)

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):
    ''' HEADERS '''
    # The input headers of the control pipeline

    # Model imports at the top of the p4 file '''
    import v1model
    z3_reg = v1model.register(z3_reg)
    # header hdr {
    #     bit<32> a;
    #     bit<32> b;
    # }
    z3_args = [('a', BitVecSort(32)), ('b', BitVecSort(32))]
    z3_reg.register_z3_type("hdr", Header, z3_args)

    ''' STRUCTS '''
    # Data structures that were declared globally

    # struct Headers {
    #     hdr h;
    # }
    z3_args = [('h', z3_reg.types["hdr"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    # struct Meta {
    # }
    z3_args = []
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

    ''' OUTPUT '''
    ''' Initialize the header  These are our inputs and outputs
     Think of it as the header inputs after they have been parsed.
     The final output of the control pipeline in a single data type.
     This corresponds to the arguments of the control function'''

    # control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm)
    z3_args = [('h', z3_reg.types["headers"]), ('m', z3_reg.types["meta"]),
               ('sm', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ''' This is the initial version of the program. '''
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):

        # @name(".NoAction") action NoAction_0() {
        # }
        def NoAction_0(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        # @name("ingress.c.a") action c_a_0() {
        #     h.h.b = h.h.a;
        # }
        def c_a_0(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                lval = "h.h.b"
                rval = "h.h.a"
                assign = AssignmentStatement(lval, rval)
                block.add(assign)
                return block
            return step(p4_vars, [BLOCK()] + expr_chain)

        # @name("ingress.c.t") table c_t {
        c_t = TableExpr("c_t")
        c_t.add_action("c_a_0", c_a_0)
        c_t.add_action("NoAction_0", NoAction_0)
        c_t.add_default(NoAction_0)

        table_key = "key_0"
        c_t.add_match(table_key)

        def BLOCK():
            block = BlockStatement()

            def BLOCK():
                block = BlockStatement()
                rval = P4Add("h.h.a", "h.h.a")
                lval = "key_0"
                assign = AssignmentStatement(lval, rval)
                block.add(assign)

                block.add(c_t.apply())

                return block
            block.add(BLOCK())

            rval = BitVecVal(0, 9)
            lval = "sm.egress_spec"
            assign = AssignmentStatement(lval, rval)

            block.add(assign)
            return block

        return BLOCK().eval(p4_vars)

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
