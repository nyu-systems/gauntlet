from p4z3_base import *


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
    z3_reg.register_z3_type("inouts", Struct, z3_args)
    ''' This is the initial version of the program. '''
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        # @name(".NoAction") action NoAction_0() {
        # }
        def NoAction_0(func_chain, p4_vars):
            ''' This is an action
                NoAction just returns the current header as is '''
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        # @name("ingress.c.a") action c_a_0() {
        #     h.h.b = h.h.a;
        # }
        def c_a_0(func_chain, p4_vars):
            ''' This is an action
                This action creates a new header type where b is set to a '''
            # This updates an existing output variable so  we need a new version
            # The new constant is appended to the existing list of constants
            # Now we create the new version by using a data type constructor
            # The data type constructor uses the values from the previous
            # variable version, except for the update target.
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = p4_vars.h.h.a
                expr = p4_vars.set("h.h.b", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)
        # @name("ingress.c.t") table c_t {

        # @name("ingress.c.t") table c_t {
        class c_t(Table):
            ''' This is a table '''
            ''' The table constant we are matching with.
             Right now, we have a hacky version of integer values which
             mimic an enum. Each integer value corresponds to a specific
             action PER table. The number of available integer values is
             constrained. '''

            @classmethod
            def table_match(cls, p4_vars):
                # The keys of the table are compared with the input keys.
                # In this case we are matching a single value
                # key = {
                #     h.h.a + h.h.a: exact @name("e") ;
                # }
                key_matches = []
                # The key is an addition of two variables
                key_0 = p4_vars.h.h.a + p4_vars.h.h.a
                key_0_match = Const(f"{cls.__name__}_key_0", key_0.sort())

                # It is an exact match, so we use direct comparison
                key_matches.append(key_0 == key_0_match)
                return And(key_matches)

            # actions = {
            #     c_a_0();
            #     NoAction_0();
            # }
            actions = {
                "c_a_0": (1, (c_a_0, ())),
                "NoAction_0": (2, (NoAction_0, ())),
            }
            actions["default"] = (0, (NoAction_0, ()))

        def apply(func_chain, p4_vars):
            ''' The main function of the control plane. Each statement in this pipe
            is part of a list of functions. '''
            sub_chain = []
            # c_t.apply();
            sub_chain.append(c_t.apply)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 9)
                expr = p4_vars.set("sm.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            # sm.egress_spec = 9w0
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)
        # return the apply function as sequence of logic clauses
        return step(func_chain=[apply], p4_vars=p4_vars)
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
    z3_reg.register_z3_type("inouts", Struct, z3_args)
    ''' This is the initial version of the program. '''
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        ''' This is the initial version of the program. '''

        # @name(".NoAction") action NoAction_0() {
        # }
        def NoAction_0(func_chain, p4_vars):
            ''' This is an action
                NoAction just returns the current header as is '''
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        # @name("ingress.c.a") action c_a_0() {
        #     h.h.b = h.h.a;
        # }
        def c_a_0(func_chain, p4_vars):
            ''' This is an action
                This action creates a new header type where b is set to a '''
            # This updates an existing output variable so  we need a new version
            # The new constant is appended to the existing list of constants
            # Now we create the new version by using a data type constructor
            # The data type constructor uses the values from the previous
            # variable version, except for the update target.
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = p4_vars.h.h.a
                expr = p4_vars.set("h.h.b", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        # The key is defined in the control function
        # Practically, this is a placeholder variable
        p4_vars.key_0 = BitVec("key_0", 32)  # bit<32> key_0;

        # @name("ingress.c.t") table c_t {
        class c_t(Table):
            ''' This is a table '''
            ''' The table constant we are matching with.
             Right now, we have a hacky version of integer values which
             mimic an enum. Each integer value corresponds to a specific
             action PER table. The number of available integer values is
             constrained. '''

            @classmethod
            def table_match(cls, p4_vars):
                name = cls.__name__
                # The keys of the table are compared with the input keys.
                # In this case we are matching a single value
                # key = {
                #     h.h.a + h.h.a: exact @name("e") ;
                # }
                key_matches = []
                # The key is an addition of two variables
                key_0 = p4_vars.h.h.a + p4_vars.h.h.a
                key_0_match = Const(f"{name}_key_0", key_0.sort())

                # It is an exact match, so we use direct comparison
                key_matches.append(key_0 == key_0_match)
                return And(key_matches)

            # actions = {
            #     c_a_0();
            #     NoAction_0();
            # }
            actions = {
                "c_a_0": (1, (c_a_0, ())),
                "NoAction_0": (2, (NoAction_0, ())),
            }
            actions["default"] = (0, (NoAction_0, ()))

        def apply(func_chain, p4_vars):
            ''' The main function of the control plane. Each statement in this pipe
            is part of a list of functions. '''
            sub_chain = []

            # {
            def block(func_chain, p4_vars):
                sub_chain = []

                def output_update(func_chain, p4_vars):
                    rval = p4_vars.h.h.a + p4_vars.h.h.a
                    expr = p4_vars.set("key_0", rval)
                    return step(func_chain, p4_vars, expr)
                # key_0 = h.h.a + h.h.a;
                sub_chain.append(output_update)
                # c_t.apply();
                sub_chain.append(c_t.apply)

                sub_chain.extend(func_chain)
                return step(sub_chain, p4_vars)
            # }
            sub_chain.append(block)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 9)
                expr = p4_vars.set("sm.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            # sm.egress_spec = 9w0
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)
        # return the apply function as sequence of logic clauses
        return apply([], p4_vars)
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


# If(And(a(hdr6192_0) + a(hdr6192_0) == key_0(c_t_m)),
#    Xor(Implies(action(c_t_m) == 1,
#                p4_vars5688_2 ==
#                mk_p4_vars(mk_headers(mk_hdr(a(hdr6192_0),
#                                         a(hdr6192_0))),
#                          mk_meta,
#                          mk_standard_metadata_t(0))),
#        Implies(action(c_t_m) == 2,
#                p4_vars5688_2 ==
#                mk_p4_vars(mk_headers(mk_hdr(a(hdr6192_0),
#                                         a(hdr6192_0))),
#                          mk_meta,
#                          mk_standard_metadata_t(0)))),
#    p4_vars5688_2 ==
#    mk_p4_vars(mk_headers(mk_hdr(a(hdr6192_0), a(hdr6192_0))),
#              mk_meta,
#              mk_standard_metadata_t(0)))
