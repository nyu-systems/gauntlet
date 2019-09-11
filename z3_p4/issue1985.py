from p4z3_base import *


def p4_program_0(z3_reg):
    ''' HEADERS '''

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('x', BitVecSort(8))]
    z3_reg.register_z3_type("h_t", Header, z3_args)

    ''' STRUCTS '''

    z3_args = [('h', z3_reg.types["h_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

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

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["meta"]),
               ('std_meta', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        def NoAction_0(func_chain, p4_vars):
            sub_chain = []

            return step(sub_chain + func_chain, p4_vars)

        def a(func_chain, p4_vars, b_1):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 8)
                expr = p4_vars.set_or_add_var("hdr.h.x", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)
            return step(sub_chain + func_chain, p4_vars)

        class t_0(Table):

            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                key_matches.append(False)
                return And(key_matches)

            actions = {
                "a": (1, (a, (Or(p4_vars.hdr.h.isValid(), True), ))),
            }
            actions["default"] = (0, (NoAction_0, ()))

        def apply(func_chain, p4_vars):
            sub_chain = []
            sub_chain.append(t_0.apply)

            return step(sub_chain + func_chain, p4_vars)
        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):
    ''' HEADERS '''

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('x', BitVecSort(8))]
    z3_reg.register_z3_type("h_t", Header, z3_args)

    ''' STRUCTS '''

    z3_args = [('h', z3_reg.types["h_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

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

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["meta"]),
               ('std_meta', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        def NoAction_0(func_chain, p4_vars):
            sub_chain = []

            return step(sub_chain + func_chain, p4_vars)

        def a(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = Or(p4_vars.hdr.h.isValid(), True)
                expr = p4_vars.set_or_add_var("b_1", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 8)
                expr = p4_vars.set_or_add_var("hdr.h.x", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)
            return step(sub_chain + func_chain, p4_vars)

        class t_0(Table):

            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                key_matches.append(False)
                return And(key_matches)

            actions = {
                "a": (1, (a, ())),
            }
            actions["default"] = (0, (NoAction_0, ()))

        def apply(func_chain, p4_vars):
            sub_chain = []
            sub_chain.append(t_0.apply)

            return step(sub_chain + func_chain, p4_vars)
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
