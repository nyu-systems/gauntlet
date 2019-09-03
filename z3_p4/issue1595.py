from p4z3_base import *


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    z3_reg.register_z3_type("Ethernet_h", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["Ethernet_h"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('a', BitVecSort(4)),
               ('b', BitVecSort(4)), ]
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

        def NoAction_0(func_chain, p4_vars):
            sub_chain = []

            return step(sub_chain + func_chain, p4_vars)

        def a1(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(1, 48)
                expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        def a2(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = slice_assign(p4_vars.hdr.ethernet.srcAddr,
                                    BitVecVal(2, 8), 47, 40)
                expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        def a3(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = slice_assign(p4_vars.hdr.ethernet.srcAddr,
                                    BitVecVal(3, 8), 47, 40)
                expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        def a4(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = slice_assign(p4_vars.hdr.ethernet.srcAddr,
                                    BitVecVal(4, 8), 47, 40)
                expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        class t1_0(Table):

            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                key_0 = p4_vars.hdr.ethernet.dstAddr
                key_0_match = Const(f"{cls.__name__}_key_0", key_0.sort())

                key_matches.append(key_0 == key_0_match)
                return And(key_matches)

            actions = {
                "a1": (1, (a1, ())),
                "a2": (2, (a2, ())),
                "a3": (3, (a3, ())),
                "a4": (4, (a4, ())),
                "NoAction_0": (5, (NoAction_0, ())),
            }
            actions["default"] = (0, (NoAction_0, ()))

        def apply(func_chain, p4_vars):
            sub_chain = []

            def switch_block(sub_chain, p4_vars):
                cases = []
                table = t1_0

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "a1", case_block)
                cases.append(case)

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.srcAddr, BitVecVal(2, 8), 39, 32)
                        expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "a2", case_block)
                cases.append(case)

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(p4_vars.hdr.ethernet.srcAddr,
                                            BitVecVal(3, 8), 39, 32)
                        expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "a3", case_block)
                cases.append(case)

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(p4_vars.hdr.ethernet.srcAddr,
                                            BitVecVal(4, 8), 39, 32)
                        expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "a4", case_block)
                cases.append(case)

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(p4_vars.hdr.ethernet.srcAddr,
                                            BitVecVal(5, 8), 39, 32)
                        expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "NoAction_0", case_block)
                cases.append(case)

                def default_case(func_chain, p4_vars):
                    sub_chain = []
                    return step(sub_chain + func_chain, p4_vars)

                return table.switch_apply(func_chain, p4_vars, cases, default_case)
            sub_chain.append(switch_block)

            return step(sub_chain + func_chain, p4_vars)
        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    z3_reg.register_z3_type("Ethernet_h", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["Ethernet_h"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('a', BitVecSort(4)),
               ('b', BitVecSort(4)), ]
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

        def NoAction_0(func_chain, p4_vars):
            sub_chain = []

            return step(sub_chain + func_chain, p4_vars)

        def a1(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(1, 48)
                expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        def a2(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = p4_vars.hdr.ethernet.srcAddr & ~BitVecVal(0xff0000000000, 48) | z3_cast(
                    BitVecVal(2, 8), 48) << 40 & BitVecVal(0xff0000000000, 48)
                expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        def a3(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = p4_vars.hdr.ethernet.srcAddr & ~BitVecVal(0xff0000000000, 48) | z3_cast(
                    BitVecVal(3, 8), 48) << 40 & BitVecVal(0xff0000000000, 48)

                expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        def a4(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = p4_vars.hdr.ethernet.srcAddr & ~BitVecVal(0xff0000000000, 48) | z3_cast(
                    BitVecVal(4, 8), 48) << 40 & BitVecVal(0xff0000000000, 48)
                expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        class t1_0(Table):

            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                key_0 = p4_vars.hdr.ethernet.dstAddr
                key_0_match = Const(f"{cls.__name__}_key_0", key_0.sort())

                key_matches.append(key_0 == key_0_match)
                return And(key_matches)

            actions = {
                "a1": (1, (a1, ())),
                "a2": (2, (a2, ())),
                "a3": (3, (a3, ())),
                "a4": (4, (a4, ())),
                "NoAction_0": (5, (NoAction_0, ())),
            }
            actions["default"] = (0, (NoAction_0, ()))

        def apply(func_chain, p4_vars):
            sub_chain = []

            def switch_block(sub_chain, p4_vars):
                cases = []
                table = t1_0

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "a1", case_block)
                cases.append(case)

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = p4_vars.hdr.ethernet.srcAddr & ~BitVecVal(0xff00000000, 48) | z3_cast(
                            BitVecVal(2, 8), 48) << 32 & BitVecVal(0xff00000000, 48)
                        expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "a2", case_block)
                cases.append(case)

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = p4_vars.hdr.ethernet.srcAddr & ~BitVecVal(0xff00000000, 48) | z3_cast(
                            BitVecVal(3, 8), 48) << 32 & BitVecVal(0xff00000000, 48)
                        expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "a3", case_block)
                cases.append(case)

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = p4_vars.hdr.ethernet.srcAddr & ~BitVecVal(0xff00000000, 48) | z3_cast(
                            BitVecVal(4, 8), 48) << 32 & BitVecVal(0xff00000000, 48)
                        expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "a4", case_block)
                cases.append(case)

                def case_block(sub_chain, p4_vars):
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = p4_vars.hdr.ethernet.srcAddr & ~BitVecVal(0xff00000000, 48) | z3_cast(
                            BitVecVal(5, 8), 48) << 32 & BitVecVal(0xff00000000, 48)
                        expr = p4_vars.set("hdr.ethernet.srcAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)
                case = table.case(
                    func_chain, p4_vars, "NoAction_0", case_block)
                cases.append(case)

                def default_case(func_chain, p4_vars):
                    sub_chain = []
                    return step(sub_chain + func_chain, p4_vars)

                return table.switch_apply(func_chain, p4_vars, cases, default_case)
            sub_chain.append(switch_block)

            return step(sub_chain + func_chain, p4_vars)
        return step(func_chain=[apply], p4_vars=p4_vars)
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
