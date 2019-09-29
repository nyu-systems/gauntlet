from p4z3_base import *


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('fA', BitVecSort(32)), ('fB', BitVecSort(16)),
               ('fC', BitVecSort(16)), ('fD', BitVecSort(16)),
               ('fE', BitVecSort(16)), ('fF', BitVecSort(32)),
               ('fG', BitVecSort(8))]
    z3_reg.register_z3_type("Hdr", Header, z3_args)

    z3_args = [('h', z3_reg.types["Hdr"])]
    z3_reg.register_z3_type("H", Struct, z3_args)

    z3_args = []
    z3_reg.register_z3_type("M", Struct, z3_args)

    z3_args = [('a', BitVecSort(8)), ('b', BitVecSort(16))]
    z3_reg.register_z3_type("FieldList1_t", Struct, z3_args)

    z3_args = [('a', BitVecSort(16)), ('b', BitVecSort(16)),
               ('c', BitVecSort(32))]
    z3_reg.register_z3_type("FieldList2_t", Struct, z3_args)

    z3_args = [('fl1', z3_reg.types["FieldList1_t"]),
               ('fl2', z3_reg.types["FieldList2_t"])]
    z3_reg.register_z3_type("FieldLists_t", Struct, z3_args)

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

    z3_args = [('hdr', z3_reg.types["H"]), ('meta', z3_reg.types["M"]),
               ('smeta', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):

        p4_vars.fl1_0 = z3_reg.instance("FieldList1_t")
        p4_vars.fl2_0 = z3_reg.instance("FieldList2_t")

        def apply(func_chain, p4_vars):
            sub_chain = []

            def struct_update(func_chain, p4_vars):
                rval = (z3_slice(p4_vars.hdr.h.fA, 31, 24),
                        p4_vars.hdr.h.fB)
                expr = p4_vars.set_struct("fl1_0", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(struct_update)

            def struct_update(func_chain, p4_vars):
                rval = (p4_vars.hdr.h.fB, p4_vars.hdr.h.fC, p4_vars.hdr.h.fA)
                expr = p4_vars.set_struct("fl2_0", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(struct_update)

            def output_update(func_chain, p4_vars):
                rval = BitVec("tmp", 16)
                expr = p4_vars.set("tmp", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.tmp
                expr = p4_vars.set("output_0", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = z3_cast(p4_vars.output_0, 9)
                expr = p4_vars.set("smeta.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)
        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('fA', BitVecSort(32)), ('fB', BitVecSort(16)),
               ('fC', BitVecSort(16)), ('fD', BitVecSort(16)),
               ('fE', BitVecSort(16)), ('fF', BitVecSort(32)),
               ('fG', BitVecSort(8))]
    z3_reg.register_z3_type("Hdr", Header, z3_args)

    z3_args = [('h', z3_reg.types["Hdr"])]
    z3_reg.register_z3_type("H", Struct, z3_args)
    z3_args = []
    z3_reg.register_z3_type("M", Struct, z3_args)

    z3_args = [('a', BitVecSort(8)), ('b', BitVecSort(16))]
    z3_reg.register_z3_type("FieldList1_t", Struct, z3_args)

    z3_args = [('a', BitVecSort(16)), ('b', BitVecSort(16)),
               ('c', BitVecSort(32))]
    z3_reg.register_z3_type("FieldList2_t", Struct, z3_args)

    z3_args = [('fl1', z3_reg.types["FieldList1_t"]),
               ('fl2', z3_reg.types["FieldList2_t"])]
    z3_reg.register_z3_type("FieldLists_t", Struct, z3_args)

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

    z3_args = [('hdr', z3_reg.types["H"]), ('meta', z3_reg.types["M"]),
               ('smeta', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):

        p4_vars.fl1_1 = z3_reg.instance("FieldList1_t")
        p4_vars.fl2_1 = z3_reg.instance("FieldList2_t")

        def apply(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = z3_slice(p4_vars.hdr.h.fA, 31, 24)
                expr = p4_vars.set("fl1_1.a", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.hdr.h.fB
                expr = p4_vars.set("fl1_1.b", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.hdr.h.fB
                expr = p4_vars.set("fl2_1.a", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.hdr.h.fC
                expr = p4_vars.set("fl2_1.b", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.hdr.h.fA
                expr = p4_vars.set("fl2_1.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVec("tmp", 16)
                expr = p4_vars.set("tmp", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = z3_cast(p4_vars.tmp, 9)
                expr = p4_vars.set("smeta.egress_spec", rval)
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
