from p4z3_base import *

def p4_program_0(z3_reg):


    import v1model
    z3_reg = v1model.register(z3_reg)


    z3_args = [
    ('x', BitVecSort(8)),
    ('y', BitVecSort(8))]
    z3_reg.register_z3_type("Meta", Struct, z3_args)

    z3_args = [
    ('a', BitVecSort(16)),
    ('b', BitVecSort(16)),
    ('c', BitVecSort(8))]
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
    z3_reg.register_z3_type("inouts", Struct, z3_args)

    ingress_args = z3_reg.instance("inouts")


    def ingress(p4_vars):
        def case0(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)


            sub_chain.extend(func_chain)

            return step(sub_chain, p4_vars)


        def case1(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)


            sub_chain.extend(func_chain)

            return step(sub_chain, p4_vars)


        def case2(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = BitVecVal(0,8)
                expr = p4_vars.set("h.h.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)


            sub_chain.extend(func_chain)

            return step(sub_chain, p4_vars)


        def case3(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = BitVecVal(0,8)
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)


            sub_chain.extend(func_chain)

            return step(sub_chain, p4_vars)


        def case4(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = BitVecVal(0,8)
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)


            sub_chain.extend(func_chain)

            return step(sub_chain, p4_vars)


        def case5(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = BitVecVal(0,8)
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)


            sub_chain.extend(func_chain)

            return step(sub_chain, p4_vars)


        def case6(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = BitVecVal(0,8)
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)


            sub_chain.extend(func_chain)

            return step(sub_chain, p4_vars)


        def case7(func_chain, p4_vars):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = BitVecVal(0,8)
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                rval = 
                expr = p4_vars.set("h.h.c", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)


            sub_chain.extend(func_chain)

            return step(sub_chain, p4_vars)



        class t_0(Table):
            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                return And(key_matches)

            actions = {
                "case0": (1, (case0, ())),
                "case1": (2, (case1, ())),
                "case2": (3, (case2, ())),
                "case3": (4, (case3, ())),
                "case4": (5, (case4, ())),
                "case5": (6, (case5, ())),
                "case6": (7, (case6, ())),
                "case7": (8, (case7, ())),
            }

            actions["default"] = (0, (case0, ()))

        def apply(func_chain, p4_vars):
            sub_chain = []
            sub_chain.append(t_0.apply)
            

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        return step(func_chain=[apply], p4_vars=p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))

