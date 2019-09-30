from p4z3_base import *


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = []
    z3_reg.register_z3_type("metadata", Struct, z3_args)

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

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["metadata"]),
               ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        def my_drop(func_chain, p4_vars, smeta):
            sub_chain = []

            return step(sub_chain + func_chain, p4_vars)

        def set_port(func_chain, p4_vars, output_port):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = output_port
                expr = p4_vars.set_or_add_var("standard_metadata.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        class mac_da_0(Table):

            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                key_0 = p4_vars.hdr.ethernet.dstAddr
                key_0_match = Const(f"{cls.__name__}_key_0", key_0.sort())

                key_matches.append(key_0 == key_0_match)
                return And(key_matches)

            actions = {
                "set_port": (1, (set_port, (BitVec("output_port", 9),))),
                "my_drop": (2, (my_drop, (p4_vars.standard_metadata.const,))),
            }
            actions["default"] = (
                0, (my_drop, (p4_vars.standard_metadata.const,)))

        def apply(func_chain, p4_vars):
            sub_chain = []
            sub_chain.append(mac_da_0.apply)

            def block(func_chain, p4_vars):
                sub_chain = []

                def output_update(func_chain, p4_vars):
                    rval = z3_slice(p4_vars.hdr.ethernet.srcAddr, 15, 0)
                    expr = p4_vars.set_or_add_var("x_0", rval)
                    return step(func_chain, p4_vars, expr)
                sub_chain.append(output_update)

                def output_update(func_chain, p4_vars):
                    rval = False
                    expr = p4_vars.set_or_add_var("hasReturned", rval)
                    return step(func_chain, p4_vars, expr)
                sub_chain.append(output_update)

                def if_block(func_chain, p4_vars):

                    condition = p4_vars.x_0 > BitVecVal(5, 16)

                    def is_true():
                        sub_chain = []

                        def output_update(func_chain, p4_vars):
                            rval = True
                            expr = p4_vars.set_or_add_var("hasReturned", rval)
                            return step(func_chain, p4_vars, expr)
                        sub_chain.append(output_update)

                        def output_update(func_chain, p4_vars):
                            rval = p4_vars.x_0 + BitVecVal(65535, 16)
                            expr = p4_vars.set_or_add_var("retval", rval)
                            return step(func_chain, p4_vars, expr)
                        sub_chain.append(output_update)

                        return step(sub_chain + func_chain, p4_vars)

                    def is_false():
                        sub_chain = []

                        def output_update(func_chain, p4_vars):
                            rval = True
                            expr = p4_vars.set_or_add_var("hasReturned", rval)
                            return step(func_chain, p4_vars, expr)
                        sub_chain.append(output_update)

                        def output_update(func_chain, p4_vars):
                            rval = p4_vars.x_0
                            expr = p4_vars.set_or_add_var("retval", rval)
                            return step(func_chain, p4_vars, expr)
                        sub_chain.append(output_update)

                        sub_chain.extend(func_chain)
                        return step(sub_chain + func_chain, p4_vars)

                    return If(condition, is_true(), is_false())
                sub_chain.append(if_block)

                def output_update(func_chain, p4_vars):
                    rval = p4_vars.retval
                    expr = p4_vars.set_or_add_var("tmp", rval)
                    return step(func_chain, p4_vars, expr)
                sub_chain.append(output_update)

                return step(sub_chain + func_chain, p4_vars)
            sub_chain.append(block)

            def output_update(func_chain, p4_vars):
                rval = slice_assign(
                    p4_vars.hdr.ethernet.srcAddr, p4_vars.tmp, 15, 0)
                expr = p4_vars.set_or_add_var("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

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

    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = []
    z3_reg.register_z3_type("metadata", Struct, z3_args)

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

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["metadata"]),
               ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        def my_drop(func_chain, p4_vars, smeta):
            sub_chain = []

            return step(sub_chain + func_chain, p4_vars)

        def set_port(func_chain, p4_vars, output_port):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = output_port
                expr = p4_vars.set_or_add_var("standard_metadata.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            return step(sub_chain + func_chain, p4_vars)

        class mac_da_0(Table):

            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                key_0 = p4_vars.hdr.ethernet.dstAddr
                key_0_match = Const(f"{cls.__name__}_key_0", key_0.sort())

                key_matches.append(key_0 == key_0_match)
                return And(key_matches)

            actions = {
                "set_port": (1, (set_port, (BitVec("output_port", 9),))),
                "my_drop": (2, (my_drop, (p4_vars.standard_metadata.const,))),
            }
            actions["default"] = (
                0, (my_drop, (p4_vars.standard_metadata.const,)))

        def apply(func_chain, p4_vars):
            sub_chain = []
            sub_chain.append(mac_da_0.apply)

            def if_block(func_chain, p4_vars):

                condition = Extract(
                    15, 0, p4_vars.hdr.ethernet.srcAddr) > BitVecVal(5, 16)

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = z3_slice(p4_vars.hdr.ethernet.srcAddr,
                                        15, 0) + BitVecVal(65535, 16)
                        expr = p4_vars.set_or_add_var("retval", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = z3_slice(p4_vars.hdr.ethernet.srcAddr,
                                        15, 0)
                        expr = p4_vars.set_or_add_var("retval", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    sub_chain.extend(func_chain)
                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.hdr.ethernet.srcAddr & ~BitVecVal(
                    0xffff, 48) | z3_cast(p4_vars.retval, 48) << 0 & BitVecVal(0xffff, 48)
                expr = p4_vars.set_or_add_var("hdr.ethernet.srcAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

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
