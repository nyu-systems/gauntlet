from p4z3_base import *


def p4_program_0(z3_reg):

    import v1model
    z3_reg = v1model.register(z3_reg)
    z3_args = [('dstAddr', BitVecSort(48)),
               ('srcAddr', BitVecSort(48)),
               ('etherType', BitVecSort(16))]
    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('tmp', BitVecSort(16)),
               ('x1', BitVecSort(32)),
               ('x2', BitVecSort(16)),
               ('x3', BitVecSort(32)),
               ('x4', BitVecSort(32)),
               ('exp_etherType', BitVecSort(16)),
               ('exp_x1', BitVecSort(32)),
               ('exp_x2', BitVecSort(16)),
               ('exp_x3', BitVecSort(32)),
               ('exp_x4', BitVecSort(32))]
    z3_reg.register_z3_type("fwd_meta_t", Struct, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('fwd_meta', z3_reg.types["fwd_meta_t"])]
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

    z3_args = [('hdr', z3_reg.types["headers"]),
               ('user_meta', z3_reg.types["metadata"]),
               ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        def NoAction_0(func_chain, p4_vars):
            sub_chain = []

            return step(sub_chain + func_chain, p4_vars)

        class debug_table_cksum1_0(Table):
            ''' This is a table '''
            ''' The table constant we are matching with.
             Right now, we have a hacky version of integer values which
             mimic an enum. Each integer value corresponds to a specific
             action PER table. The number of available integer values is
             constrained. '''

            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                key_0 = p4_vars.hdr.ethernet.srcAddr
                key_0_match = Const(f"{cls.__name__}_key_0", key_0.sort())
                key_matches.append(key_0 == key_0_match)

                key_1 = p4_vars.hdr.ethernet.dstAddr
                key_1_match = Const(f"{cls.__name__}_key_1", key_1.sort())
                key_matches.append(key_1 == key_1_match)

                key_2 = p4_vars.hdr.ethernet.etherType
                key_2_match = Const(f"{cls.__name__}_key_2", key_2.sort())
                key_matches.append(key_2 == key_2_match)

                key_3 = p4_vars.user_meta.fwd_meta.exp_etherType
                key_3_match = Const(f"{cls.__name__}_key_3", key_3.sort())
                key_matches.append(key_3 == key_3_match)

                key_4 = p4_vars.user_meta.fwd_meta.tmp
                key_4_match = Const(f"{cls.__name__}_key_4", key_4.sort())
                key_matches.append(key_4 == key_4_match)

                key_5 = p4_vars.user_meta.fwd_meta.exp_x1
                key_5_match = Const(f"{cls.__name__}_key_5", key_5.sort())
                key_matches.append(key_5 == key_5_match)

                key_6 = p4_vars.user_meta.fwd_meta.x1
                key_6_match = Const(f"{cls.__name__}_key_6", key_6.sort())
                key_matches.append(key_6 == key_6_match)

                key_7 = p4_vars.user_meta.fwd_meta.exp_x2
                key_7_match = Const(f"{cls.__name__}_key_7", key_7.sort())
                key_matches.append(key_7 == key_7_match)

                key_8 = p4_vars.user_meta.fwd_meta.x2
                key_8_match = Const(f"{cls.__name__}_key_8", key_8.sort())
                key_matches.append(key_8 == key_8_match)

                key_9 = p4_vars.user_meta.fwd_meta.exp_x3
                key_9_match = Const(f"{cls.__name__}_key_9", key_9.sort())
                key_matches.append(key_9 == key_9_match)

                key_10 = p4_vars.user_meta.fwd_meta.x3
                key_10_match = Const(f"{cls.__name__}_key_10", key_10.sort())
                key_matches.append(key_10 == key_10_match)

                key_11 = p4_vars.user_meta.fwd_meta.exp_x4
                key_11_match = Const(f"{cls.__name__}_key_11", key_11.sort())
                key_matches.append(key_11 == key_11_match)

                key_12 = p4_vars.user_meta.fwd_meta.x4
                key_12_match = Const(f"{cls.__name__}_key_12", key_12.sort())
                key_matches.append(key_12 == key_12_match)

                return And(key_matches)

            actions = {
                "NoAction_0": (1, (NoAction_0, ())),
            }
            actions["default"] = (0, (NoAction_0, ()))

        def apply(func_chain, p4_vars):
            ''' The main function of the control plane. Each statement in this pipe
            is part of a list of functions. '''
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = ~p4_vars.hdr.ethernet.etherType
                expr = p4_vars.set("tmp_0", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = z3_cast(p4_vars.tmp_0, 32)
                expr = p4_vars.set("x1_0", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = z3_slice(p4_vars.x1_0, 31, 16) + \
                    z3_slice(p4_vars.x1_0, 15, 0)
                expr = p4_vars.set("x2_0", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.tmp_0
                expr = p4_vars.set("user_meta.fwd_meta.tmp", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.x1_0
                expr = p4_vars.set("user_meta.fwd_meta.x1", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = p4_vars.x2_0
                expr = p4_vars.set("user_meta.fwd_meta.x2", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = z3_cast(~p4_vars.hdr.ethernet.etherType, 32)
                expr = p4_vars.set("user_meta.fwd_meta.x3", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = ~z3_cast(p4_vars.hdr.ethernet.etherType, 32)

                expr = p4_vars.set("user_meta.fwd_meta.x4", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0x800, 16)
                expr = p4_vars.set("user_meta.fwd_meta.exp_etherType", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0xf7ff, 32)
                expr = p4_vars.set("user_meta.fwd_meta.exp_x1", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0xf7ff, 16)
                expr = p4_vars.set("user_meta.fwd_meta.exp_x2", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0xf7ff, 32)
                expr = p4_vars.set("user_meta.fwd_meta.exp_x3", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0xfffff7ff, 32)
                expr = p4_vars.set("user_meta.fwd_meta.exp_x4", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 48)
                expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def if_block(func_chain, p4_vars):

                condition = (p4_vars.hdr.ethernet.etherType !=
                             p4_vars.user_meta.fwd_meta.exp_etherType)

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 47, 40)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []

                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def if_block(func_chain, p4_vars):

                condition = (p4_vars.user_meta.fwd_meta.x1 !=
                             p4_vars.user_meta.fwd_meta.exp_x1)

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 39, 32)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []
                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def if_block(func_chain, p4_vars):

                condition = (p4_vars.user_meta.fwd_meta.x2 !=
                             p4_vars.user_meta.fwd_meta.exp_x2)

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 31, 24)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []
                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def if_block(func_chain, p4_vars):

                condition = (p4_vars.user_meta.fwd_meta.x3 !=
                             p4_vars.user_meta.fwd_meta.exp_x3)

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 23, 16)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []
                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def if_block(func_chain, p4_vars):

                condition = (p4_vars.user_meta.fwd_meta.x4 !=
                             p4_vars.user_meta.fwd_meta.exp_x4)

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 15, 8)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []
                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            sub_chain.append(debug_table_cksum1_0.apply)

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

    z3_args = [('tmp', BitVecSort(16)),
               ('x1', BitVecSort(32)),
               ('x2', BitVecSort(16)),
               ('x3', BitVecSort(32)),
               ('x4', BitVecSort(32)),
               ('exp_etherType', BitVecSort(16)),
               ('exp_x1', BitVecSort(32)),
               ('exp_x2', BitVecSort(16)),
               ('exp_x3', BitVecSort(32)),
               ('exp_x4', BitVecSort(32))]
    z3_reg.register_z3_type("fwd_meta_t", Struct, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('fwd_meta', z3_reg.types["fwd_meta_t"])]
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

    z3_args = [('hdr', z3_reg.types["headers"]),
               ('user_meta', z3_reg.types["metadata"]),
               ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

    def ingress(p4_vars):
        def NoAction_0(func_chain, p4_vars):
            sub_chain = []

            return step(sub_chain + func_chain, p4_vars)

        class debug_table_cksum1_0(Table):
            ''' This is a table '''
            ''' The table constant we are matching with.
             Right now, we have a hacky version of integer values which
             mimic an enum. Each integer value corresponds to a specific
             action PER table. The number of available integer values is
             constrained. '''

            @classmethod
            def table_match(cls, p4_vars):
                key_matches = []
                key_0 = p4_vars.hdr.ethernet.srcAddr
                key_0_match = Const(f"{cls.__name__}_key_0", key_0.sort())
                key_matches.append(key_0 == key_0_match)

                key_1 = p4_vars.hdr.ethernet.dstAddr
                key_1_match = Const(f"{cls.__name__}_key_1", key_1.sort())
                key_matches.append(key_1 == key_1_match)

                key_2 = p4_vars.hdr.ethernet.etherType
                key_2_match = Const(f"{cls.__name__}_key_2", key_2.sort())
                key_matches.append(key_2 == key_2_match)

                key_3 = p4_vars.user_meta.fwd_meta.exp_etherType
                key_3_match = Const(f"{cls.__name__}_key_3", key_3.sort())
                key_matches.append(key_3 == key_3_match)

                key_4 = p4_vars.user_meta.fwd_meta.tmp
                key_4_match = Const(f"{cls.__name__}_key_4", key_4.sort())
                key_matches.append(key_4 == key_4_match)

                key_5 = p4_vars.user_meta.fwd_meta.exp_x1
                key_5_match = Const(f"{cls.__name__}_key_5", key_5.sort())
                key_matches.append(key_5 == key_5_match)

                key_6 = p4_vars.user_meta.fwd_meta.x1
                key_6_match = Const(f"{cls.__name__}_key_6", key_6.sort())
                key_matches.append(key_6 == key_6_match)

                key_7 = p4_vars.user_meta.fwd_meta.exp_x2
                key_7_match = Const(f"{cls.__name__}_key_7", key_7.sort())
                key_matches.append(key_7 == key_7_match)

                key_8 = p4_vars.user_meta.fwd_meta.x2
                key_8_match = Const(f"{cls.__name__}_key_8", key_8.sort())
                key_matches.append(key_8 == key_8_match)

                key_9 = p4_vars.user_meta.fwd_meta.exp_x3
                key_9_match = Const(f"{cls.__name__}_key_9", key_9.sort())
                key_matches.append(key_9 == key_9_match)

                key_10 = p4_vars.user_meta.fwd_meta.x3
                key_10_match = Const(f"{cls.__name__}_key_10", key_10.sort())
                key_matches.append(key_10 == key_10_match)

                key_11 = p4_vars.user_meta.fwd_meta.exp_x4
                key_11_match = Const(f"{cls.__name__}_key_11", key_11.sort())
                key_matches.append(key_11 == key_11_match)

                key_12 = p4_vars.user_meta.fwd_meta.x4
                key_12_match = Const(f"{cls.__name__}_key_12", key_12.sort())
                key_matches.append(key_12 == key_12_match)

                return And(key_matches)

            actions = {
                "NoAction_0": (1, (NoAction_0, ())),
            }
            actions["default"] = (0, (NoAction_0, ()))

        def apply(func_chain, p4_vars):
            ''' The main function of the control plane. Each statement in this pipe
            is part of a list of functions. '''
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = ~p4_vars.hdr.ethernet.etherType
                expr = p4_vars.set("user_meta.fwd_meta.tmp", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = z3_cast(~p4_vars.hdr.ethernet.etherType, 32)
                expr = p4_vars.set("user_meta.fwd_meta.x1", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = z3_slice(z3_cast(p4_vars.hdr.ethernet.etherType, 32), 31, 16) + \
                    z3_slice(z3_cast(~p4_vars.hdr.ethernet.etherType, 32), 15, 0)
                expr = p4_vars.set("user_meta.fwd_meta.x2", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = z3_cast(~p4_vars.hdr.ethernet.etherType, 32)
                expr = p4_vars.set("user_meta.fwd_meta.x3", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = ~z3_cast(p4_vars.hdr.ethernet.etherType, 32)

                expr = p4_vars.set("user_meta.fwd_meta.x4", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0x800, 16)
                expr = p4_vars.set("user_meta.fwd_meta.exp_etherType", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0xf7ff, 32)
                expr = p4_vars.set("user_meta.fwd_meta.exp_x1", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0xf7ff, 16)
                expr = p4_vars.set("user_meta.fwd_meta.exp_x2", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0xf7ff, 32)
                expr = p4_vars.set("user_meta.fwd_meta.exp_x3", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0xfffff7ff, 32)
                expr = p4_vars.set("user_meta.fwd_meta.exp_x4", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVecVal(0, 48)
                expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def if_block(func_chain, p4_vars):

                condition = (p4_vars.hdr.ethernet.etherType !=
                             BitVecVal(0x800, 16))

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 47, 40)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []

                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def if_block(func_chain, p4_vars):

                condition = (z3_cast(~p4_vars.hdr.ethernet.etherType, 32) !=
                             BitVecVal(0xf7ff, 32))

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 39, 32)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []

                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def if_block(func_chain, p4_vars):

                condition = (z3_slice(z3_cast(~p4_vars.hdr.ethernet.etherType, 32), 31, 16) + z3_slice(z3_cast(~p4_vars.hdr.ethernet.etherType, 32), 15, 0) !=
                             BitVecVal(0xf7ff, 16))

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 31, 24)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []

                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def if_block(func_chain, p4_vars):

                condition = (z3_cast(~p4_vars.hdr.ethernet.etherType, 32) !=
                             BitVecVal(0xf7ff, 32))

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 23, 16)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []
                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            def if_block(func_chain, p4_vars):

                condition = (~z3_cast(p4_vars.hdr.ethernet.etherType, 32) !=
                             BitVecVal(0xfffff7ff, 32))

                def is_true():
                    sub_chain = []

                    def output_update(func_chain, p4_vars):
                        rval = slice_assign(
                            p4_vars.hdr.ethernet.dstAddr, BitVecVal(1, 8), 15, 8)
                        expr = p4_vars.set("hdr.ethernet.dstAddr", rval)
                        return step(func_chain, p4_vars, expr)
                    sub_chain.append(output_update)

                    return step(sub_chain + func_chain, p4_vars)

                def is_false():
                    sub_chain = []

                    return step(sub_chain + func_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            sub_chain.append(debug_table_cksum1_0.apply)

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
