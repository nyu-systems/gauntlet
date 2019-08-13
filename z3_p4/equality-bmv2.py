from p4z3_base import *


def p4_program_0(Z3Reg):
    Z3Reg.reset()

    import v1model
    Z3Reg = v1model.register(Z3Reg)

    z3_args = [('s', BitVecSort(8)), ('v', BitVecSort(32))]
    Z3Reg.register_z3_type("H", Header, z3_args)

    z3_args = [('same', BitVecSort(8))]
    Z3Reg.register_z3_type("Same", Header, z3_args)

    z3_args = [('h', Z3Reg.types["H"]), ] + [(f"a_{i}", Z3Reg.types["H"]) for i in range(2)] + [('same', Z3Reg.types["Same"])]
    Z3Reg.register_z3_type("headers", Struct, z3_args)

    z3_args = []
    Z3Reg.register_z3_type("metadata", Struct, z3_args)

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

    z3_args = [('hdr', Z3Reg.types["headers"]), ('meta', Z3Reg.types["metadata"]),
               ('stdmeta', Z3Reg.types["standard_metadata_t"])]
    Z3Reg.register_z3_type("inouts", Struct, z3_args)
    ingress_args = Z3Reg.classes["inouts"]()

    def ingress(p4_vars):

        for i in range(2):
            setattr(p4_vars, f"tmp_{i}", Z3Reg.classes["H"](i + 1))

        def apply(func_chain, p4_vars):
            sub_chain = []
            p4_vars.hdr.same.setValid()

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 8)
                expr = p4_vars.set("hdr.same.same", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 9)
                expr = p4_vars.set("stdmeta.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def if_block(func_chain, p4_vars):

                condition = (p4_vars.hdr.h.s == p4_vars.hdr.a_0.s)

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = p4_vars.hdr.same.same | BitVecVal(1, 8)
                        expr = p4_vars.set("hdr.same.same", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    sub_chain.extend(func_chain)
                    return step(sub_chain, p4_vars)

                def is_false():
                    sub_chain = []
                    sub_chain.extend(func_chain)
                    return step(sub_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            # def if_block(func_chain, p4_vars):

            #     condition = (p4_vars.hdr.h.v == p4_vars.hdr.a_0.v)

            #     def is_true():
            #         sub_chain = []

            #         def output_update(func_chain, p4_vars):
            #             rval = p4_vars.hdr.same.same | BitVecVal(2, 8)
            #             expr = p4_vars.set("hdr.same.same", rval)
            #             return step(func_chain, p4_vars, expr)
            #         sub_chain.append(output_update)

            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     def is_false():
            #         sub_chain = []
            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     return If(condition, is_true(), is_false())
            # sub_chain.append(if_block)

            # def if_block(func_chain, p4_vars):

            #     condition = And(And(And(Or(And(Not(p4_vars.hdr.h.isValid()),
            #                                    Not(p4_vars.hdr.a_0.isValid())),
            #                                p4_vars.hdr.h.isValid()),
            #                             p4_vars.hdr.a_0.isValid()),
            #                         p4_vars.hdr.h.s == p4_vars.hdr.a_0.s),
            #                     p4_vars.hdr.h.v == p4_vars.hdr.a_0.v)

            #     def is_true():
            #         sub_chain = []

            #         def output_update(func_chain, p4_vars):
            #             rval = p4_vars.hdr.same.same | BitVecVal(4, 8)
            #             expr = p4_vars.set("hdr.same.same", rval)
            #             return step(func_chain, p4_vars, expr)
            #         sub_chain.append(output_update)

            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     def is_false():
            #         sub_chain = []
            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     return If(condition, is_true(), is_false())
            # sub_chain.append(if_block)

            # def output_update(func_chain, p4_vars):
            #     rval = p4_vars.hdr.h
            #     expr = p4_vars.set("tmp_0", rval)
            #     return step(func_chain, p4_vars, expr)
            # sub_chain.append(output_update)

            # def output_update(func_chain, p4_vars):
            #     rval = p4_vars.hdr.a_0
            #     expr = p4_vars.set("tmp_1", rval)
            #     return step(func_chain, p4_vars, expr)
            # sub_chain.append(output_update)

            # sub_chain.extend(func_chain)

            # def if_block(func_chain, p4_vars):

            #     condition = And(And(And(And(Or(And
            #                                    (Not(p4_vars.tmp_0.isValid()), Not(
            #                                        p4_vars.hdr.a_0.isValid())),
            #                                    p4_vars.tmp_0.isValid()),
            #                                 p4_vars.hdr.a_0.isValid()),
            #                             p4_vars.tmp_0.s == p4_vars.hdr.a_0.s),
            #                         p4_vars.tmp_0.v == p4_vars.hdr.a_0.v),
            #                     And(And(And(Or(And(Not(p4_vars.tmp_1.isValid()),
            #                                        Not(p4_vars.hdr.a_1.isValid())),
            #                                    p4_vars.tmp_1.isValid()),
            #                                 p4_vars.hdr.a_1.isValid()),
            #                             p4_vars.tmp_1.s == p4_vars.hdr.a_1.s),
            #                         p4_vars.tmp_1.v == p4_vars.hdr.a_1.v))

            #     def is_true():
            #         sub_chain = []

            #         def output_update(func_chain, p4_vars):
            #             rval = p4_vars.hdr.same.same | BitVecVal(4, 8)
            #             expr = p4_vars.set("hdr.same.same", rval)
            #             return step(func_chain, p4_vars, expr)
            #         sub_chain.append(output_update)

            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     def is_false():
            #         sub_chain = []
            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     return If(condition, is_true(), is_false())
            # sub_chain.append(if_block)

            return step(sub_chain, p4_vars)
        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(Z3Reg):
    Z3Reg.reset()

    import v1model
    Z3Reg = v1model.register(Z3Reg)

    z3_args = [('s', BitVecSort(8)), ('v', BitVecSort(32))]
    Z3Reg.register_z3_type("H", Header, z3_args)

    z3_args = [('same', BitVecSort(8))]
    Z3Reg.register_z3_type("Same", Header, z3_args)

    z3_args = [('h', Z3Reg.types["H"]), ] + [(f"a_{i}", Z3Reg.types["H"]) for i in range(2)] + [('same', Z3Reg.types["Same"])]
    Z3Reg.register_z3_type("headers", Struct, z3_args)

    z3_args = []
    Z3Reg.register_z3_type("metadata", Struct, z3_args)

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

    z3_args = [('hdr', Z3Reg.types["headers"]), ('meta', Z3Reg.types["metadata"]),
               ('stdmeta', Z3Reg.types["standard_metadata_t"])]
    Z3Reg.register_z3_type("inouts", Struct, z3_args)
    ingress_args = Z3Reg.classes["inouts"]()

    def ingress(p4_vars):

        for i in range(2):
            setattr(p4_vars, f"tmp_{i}", Z3Reg.classes["H"](i))

        def apply(func_chain, p4_vars):
            sub_chain = []
            p4_vars.hdr.same.setValid()

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 8)
                expr = p4_vars.set("hdr.same.same", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 9)
                expr = p4_vars.set("stdmeta.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def if_block(func_chain, p4_vars):

                condition = (p4_vars.hdr.h.s == p4_vars.hdr.a_0.s)

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = p4_vars.hdr.same.same | BitVecVal(1, 8)
                        expr = p4_vars.set("hdr.same.same", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    sub_chain.extend(func_chain)
                    return step(sub_chain, p4_vars)

                def is_false():
                    sub_chain = []
                    sub_chain.extend(func_chain)
                    return step(sub_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            # def if_block(func_chain, p4_vars):

            #     condition = (p4_vars.hdr.h.v == p4_vars.hdr.a_0.v)

            #     def is_true():
            #         sub_chain = []

            #         def output_update(func_chain, p4_vars):
            #             rval = p4_vars.hdr.same.same | BitVecVal(2, 8)
            #             expr = p4_vars.set("hdr.same.same", rval)
            #             return step(func_chain, p4_vars, expr)
            #         sub_chain.append(output_update)

            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     def is_false():
            #         sub_chain = []
            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     return If(condition, is_true(), is_false())
            # sub_chain.append(if_block)

            # def if_block(func_chain, p4_vars):

            #     condition = And(And(And(Or(And(Not(p4_vars.hdr.h.isValid()),
            #                                    Not(p4_vars.hdr.a_0.isValid())),
            #                                p4_vars.hdr.h.isValid()),
            #                             p4_vars.hdr.a_0.isValid()),
            #                         p4_vars.hdr.h.s == p4_vars.hdr.a_0.s),
            #                     p4_vars.hdr.h.v == p4_vars.hdr.a_0.v)

            #     def is_true():
            #         sub_chain = []

            #         def output_update(func_chain, p4_vars):
            #             rval = p4_vars.hdr.same.same | BitVecVal(4, 8)
            #             expr = p4_vars.set("hdr.same.same", rval)
            #             return step(func_chain, p4_vars, expr)
            #         sub_chain.append(output_update)

            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     def is_false():
            #         sub_chain = []
            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     return If(condition, is_true(), is_false())
            # sub_chain.append(if_block)

            # def output_update(func_chain, p4_vars):
            #     rval = p4_vars.hdr.h
            #     expr = p4_vars.set("tmp_0", rval)
            #     return step(func_chain, p4_vars, expr)
            # sub_chain.append(output_update)

            # def output_update(func_chain, p4_vars):
            #     rval = p4_vars.hdr.a_0
            #     expr = p4_vars.set("tmp_1", rval)
            #     return step(func_chain, p4_vars, expr)
            # sub_chain.append(output_update)

            # sub_chain.extend(func_chain)

            # def if_block(func_chain, p4_vars):

            #     condition = And(And(And(And(Or(And
            #                                    (Not(p4_vars.tmp_0.isValid()), Not(
            #                                        p4_vars.hdr.a_0.isValid())),
            #                                    p4_vars.tmp_0.isValid()),
            #                                 p4_vars.hdr.a_0.isValid()),
            #                             p4_vars.tmp_0.s == p4_vars.hdr.a_0.s),
            #                         p4_vars.tmp_0.v == p4_vars.hdr.a_0.v),
            #                     And(And(And(Or(And(Not(p4_vars.tmp_1.isValid()),
            #                                        Not(p4_vars.hdr.a_1.isValid())),
            #                                    p4_vars.tmp_1.isValid()),
            #                                 p4_vars.hdr.a_1.isValid()),
            #                             p4_vars.tmp_1.s == p4_vars.hdr.a_1.s),
            #                         p4_vars.tmp_1.v == p4_vars.hdr.a_1.v))

            #     def is_true():
            #         sub_chain = []

            #         def output_update(func_chain, p4_vars):
            #             rval = p4_vars.hdr.same.same | BitVecVal(4, 8)
            #             expr = p4_vars.set("hdr.same.same", rval)
            #             return step(func_chain, p4_vars, expr)
            #         sub_chain.append(output_update)

            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     def is_false():
            #         sub_chain = []
            #         sub_chain.extend(func_chain)
            #         return step(sub_chain, p4_vars)

            #     return If(condition, is_true(), is_false())
            # sub_chain.append(if_block)

            return step(sub_chain, p4_vars)
        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def z3_check():
    s = Solver()

    p4_ctrl_0, p4_ctrl_0_args = p4_program_0(Z3Reg)[2]
    p4_ctrl_1, p4_ctrl_1_args = p4_program_1(Z3Reg)[2]

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
