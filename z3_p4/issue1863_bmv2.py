from p4z3_base import *


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('dstAddr', BitVecSort(48)),
               ('srcAddr', BitVecSort(48)),
               ('etherType', BitVecSort(16))]
    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('a', BitVecSort(8)),
               ('b', BitVecSort(8))]
    z3_reg.register_z3_type("custom_t", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"]),
               ('custom', z3_reg.types["custom_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('a', BitVecSort(8)),
               ('b', BitVecSort(8))]
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

    def ingress(p4_vars):

        p4_vars.foo_0 = z3_reg.instance("foo_t")

        def apply(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 9)
                expr = p4_vars.set("stdmeta.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def struct_update(func_chain, p4_vars):
                rval = (BitVecVal(1, 8), BitVecVal(2, 8))
                expr = p4_vars.set_struct("foo_0", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(struct_update)

            def struct_update(func_chain, p4_vars):
                rval = (p4_vars.foo_0.b, p4_vars.foo_0.a)
                expr = p4_vars.set_struct("foo_0", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(struct_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.foo_0.a
                expr = p4_vars.set("hdr.custom.a", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.foo_0.b
                expr = p4_vars.set("hdr.custom.b", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)
        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('dstAddr', BitVecSort(48)),
               ('srcAddr', BitVecSort(48)),
               ('etherType', BitVecSort(16))]
    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('a', BitVecSort(8)),
               ('b', BitVecSort(8))]
    z3_reg.register_z3_type("custom_t", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"]),
               ('custom', z3_reg.types["custom_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('a', BitVecSort(8)),
               ('b', BitVecSort(8))]
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

    def ingress(p4_vars):

        p4_vars.foo_0 = z3_reg.instance("foo_t")

        def apply(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 9)
                expr = p4_vars.set("stdmeta.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(1, 8)
                expr = p4_vars.set("foo_0.a", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(2, 8)
                expr = p4_vars.set("foo_0.b", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.foo_0.b
                expr = p4_vars.set("foo_0.a", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.foo_0.a
                expr = p4_vars.set("foo_0.b", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.foo_0.a
                expr = p4_vars.set("hdr.custom.a", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.foo_0.b
                expr = p4_vars.set("hdr.custom.b", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

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
