from p4z3_base import *


def p4_program_0(Z3Reg):
    Z3Reg.reset()

    ''' HEADERS '''
    # The input headers of the control pipeline
    # Model imports at the top of the p4 file '''
    import v1model
    Z3Reg = v1model.register(Z3Reg)

    z3_args = [
        ('vrf', BitVecSort(12)),
        ('bd', BitVecSort(16)),
        ('nexthop_index', BitVecSort(16))
    ]

    Z3Reg.register_z3_type("ingress_metadata_t", Struct, z3_args)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    Z3Reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('version', BitVecSort(4)), ('ihl', BitVecSort(4)),
               ('diffserv', BitVecSort(8)), ('totalLen', BitVecSort(16)),
               ('identification', BitVecSort(16)), ('flags', BitVecSort(3)),
               ('fragOffset', BitVecSort(13)), ('ttl', BitVecSort(8)),
               ('protocol', BitVecSort(8)), ('hdrChecksum', BitVecSort(16)),
               ('srcAddr', BitVecSort(32)), ('dstAddr', BitVecSort(32))
               ]
    Z3Reg.register_z3_type("ipv4_t", Header, z3_args)

    z3_args = [('ingress_metadata', Z3Reg.reg["ingress_metadata_t"])]
    Z3Reg.register_z3_type("metadata", Struct, z3_args)

    z3_args = [('ethernet', Z3Reg.reg["ethernet_t"]),
               ('ipv4', Z3Reg.reg["ipv4_t"])]
    Z3Reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('hdr', Z3Reg.reg["headers"]), ('meta', Z3Reg.reg["metadata"]),
               ('standard_metadata', Z3Reg.reg["standard_metadata_t"])]
    Z3Reg.register_z3_type("inouts", Struct, z3_args)
    ingress_args = Z3Reg.reg["INOUTS"]()

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

    def ingress(p4_vars):
        def NoAction_1(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def NoAction_8(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def NoAction_9(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def NoAction_10(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def NoAction_11(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def set_vrf(func_chain, p4_vars, vrf):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = vrf
                expr = p4_vars.set("meta.ingress_metadata.vrf", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def on_miss_2(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def on_miss_5(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def on_miss_6(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def fib_hit_nexthop(func_chain, p4_vars, nexthop_index):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = nexthop_index
                expr = p4_vars.set("meta.ingress_metadata.nexthop_index", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVec(255, 8)
                expr = p4_vars.set("hdr.ipv4.ttl", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def fib_hit_nexthop_2(func_chain, p4_vars, nexthop_index):

            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = nexthop_index
                expr = p4_vars.set("meta.ingress_metadata.nexthop_index", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVec(255, 8)
                expr = p4_vars.set("hdr.ipv4.ttl", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def set_egress_details(func_chain, p4_vars, egress_spec):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = egress_spec
                expr = p4_vars.set("standard_metadata.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def set_bd(func_chain, p4_vars, bd):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = bd
                expr = p4_vars.set("meta.ingress_metadata.bd", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        class bd_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                bd_0_key_0 = p4_vars.meta.ingress_metadata.bd
                bd_0_key_0_const = Const("bd_0_key_0", bd_0_key_0.sort())
                key_matches.append(bd_0_key_0 == bd_0_key_0_const)
                return And(key_matches)

            actions = {
                "set_vrf": (1, (set_vrf, [BitVec("bd_0_vrf", 12)])),
            }
            actions["default"] = (0, (NoAction_1, ()))

        class ipv4_fib_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                ipv4_fib_0_key_0 = p4_vars.meta.ingress_metadata.vrf
                ipv4_fib_0_key_0_const = Const(
                    "ipv4_fib_0_key_0", ipv4_fib_0_key_0.sort())
                key_matches.append(ipv4_fib_0_key_0 == ipv4_fib_0_key_0_const)

                ipv4_fib_0_key_1 = p4_vars.hdr.ipv4.dstAddr
                ipv4_fib_0_key_1_const = Const(
                    "ipv4_fib_0_key_1", ipv4_fib_0_key_1.sort())
                key_matches.append(ipv4_fib_0_key_1 == ipv4_fib_0_key_1_const)
                return And(key_matches)

            actions = {
                "on_miss_2": (1, (on_miss_2, ())),
                "fib_hit_nexthop": (2, (fib_hit_nexthop, [BitVec("ipv4_fib_0_nexthop_index", 16)])),
            }
            actions["default"] = (0, (NoAction_8, ()))

        class ipv4_fib_lpm_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                ipv4_fib_lpm_0_key_0 = p4_vars.meta.ingress_metadata.vrf
                ipv4_fib_lpm_0_key_0_const = Const(
                    "ipv4_fib_lpm_0_key_0", ipv4_fib_lpm_0_key_0.sort())
                key_matches.append(ipv4_fib_lpm_0_key_0 ==
                                   ipv4_fib_lpm_0_key_0_const)

                # This should be a mask for lpm matches
                # TODO: Make it a proper mask and fix, not sure how yet
                masks = [int("0x" + ((32 // 4) - i) * "0" +
                             i * "f", 16) for i in range(1, 32 // 4 + 1)]
                ipv4_fib_lpm_0_key_1 = p4_vars.hdr.ipv4.dstAddr
                ipv4_fib_lpm_0_key_1_const = Const(
                    "ipv4_fib_lpm_0_key_1", ipv4_fib_lpm_0_key_1.sort())
                key_matches.append(Or([ipv4_fib_lpm_0_key_1 & m ==
                                       ipv4_fib_lpm_0_key_1_const & m
                                       for m in masks]))
                return And(key_matches)

            actions = {
                "on_miss_5": (1, (on_miss_5, ())),
                "fib_hit_nexthop_2": (2, (fib_hit_nexthop_2,
                                          [BitVec("ipv4_fib_lpm_0_nexthop_index",
                                                  16)]))
            }
            actions["default"] = (0, (NoAction_9, ()))

        class nexthop_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                nexthop_0_key_0 = p4_vars.meta.ingress_metadata.nexthop_index
                nexthop_0_key_0_const = Const(
                    "nexthop_0_key_0", nexthop_0_key_0.sort())
                key_matches.append(nexthop_0_key_0 == nexthop_0_key_0_const)
                return And(key_matches)

            actions = {
                "on_miss_6": (1, (on_miss_6, ())),
                "set_egress_details": (2, (set_egress_details, [BitVec("nexthop_0_egress_spec", 9)])),
            }
            actions["default"] = (0, (NoAction_10, ()))

        class port_mapping_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                port_mapping_0_key_0 = p4_vars.standard_metadata.ingress_port
                port_mapping_0_key_0_const = Const(
                    "port_mapping_0_key_0", port_mapping_0_key_0.sort())
                key_matches.append(port_mapping_0_key_0 ==
                                   port_mapping_0_key_0_const)
                return And(key_matches)

            actions = {
                "set_bd": (1, (set_bd, [BitVec("port_mapping_0_bd", 16)])),
            }
            actions["default"] = (0, (NoAction_11, ()))

        def apply(func_chain, p4_vars):
            sub_chain = []

            def if_block(func_chain, p4_vars):

                condition = p4_vars.hdr.ipv4.isValid()

                def is_true():
                    sub_chain = []

                    sub_chain.append(port_mapping_0.apply)
                    sub_chain.append(bd_0.apply)

                    sub_chain.append(ipv4_fib_0.apply)

                    def switch_block(sub_chain, p4_vars):
                        cases = []
                        switch = ipv4_fib_0.action_run(p4_vars)
                        a = ipv4_fib_0.actions

                        def case_block(sub_chain, p4_vars):
                            sub_chain = []

                            sub_chain.append(ipv4_fib_lpm_0.apply)

                            sub_chain.extend(func_chain)
                            return step(sub_chain, p4_vars)
                        case = Implies(
                            switch == a["on_miss_2"][0],
                            case_block(func_chain, p4_vars))
                        cases.append(case)

                        default = step(func_chain, p4_vars)

                        return And(*cases, default)
                    sub_chain.append(switch_block)

                    sub_chain.extend(func_chain)
                    return step(sub_chain, p4_vars)

                def is_false():
                    sub_chain = []

                    sub_chain.extend(func_chain)
                    return step(sub_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            sub_chain.append(nexthop_0.apply)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)
        return apply([], p4_vars)
    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(Z3Reg):
    Z3Reg.reset()

    ''' HEADERS '''
    # The input headers of the control pipeline
    # Model imports at the top of the p4 file '''
    import v1model
    Z3Reg = v1model.register(Z3Reg)

    z3_args = [
        ('vrf', BitVecSort(12)),
        ('bd', BitVecSort(16)),
        ('nexthop_index', BitVecSort(16))
    ]

    Z3Reg.register_z3_type("ingress_metadata_t", Struct, z3_args)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    Z3Reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('version', BitVecSort(4)), ('ihl', BitVecSort(4)),
               ('diffserv', BitVecSort(8)), ('totalLen', BitVecSort(16)),
               ('identification', BitVecSort(16)), ('flags', BitVecSort(3)),
               ('fragOffset', BitVecSort(13)), ('ttl', BitVecSort(8)),
               ('protocol', BitVecSort(8)), ('hdrChecksum', BitVecSort(16)),
               ('srcAddr', BitVecSort(32)), ('dstAddr', BitVecSort(32))
               ]
    Z3Reg.register_z3_type("ipv4_t", Header, z3_args)

    z3_args = [('ingress_metadata', Z3Reg.reg["ingress_metadata_t"])]
    Z3Reg.register_z3_type("metadata", Struct, z3_args)

    z3_args = [('ethernet', Z3Reg.reg["ethernet_t"]),
               ('ipv4', Z3Reg.reg["ipv4_t"])]
    Z3Reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('hdr', Z3Reg.reg["headers"]), ('meta', Z3Reg.reg["metadata"]),
               ('standard_metadata', Z3Reg.reg["standard_metadata_t"])]
    Z3Reg.register_z3_type("inouts", Struct, z3_args)
    ingress_args = Z3Reg.reg["INOUTS"]()

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

    def ingress(p4_vars):
        def NoAction_1(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def NoAction_8(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def NoAction_9(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def NoAction_10(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def NoAction_11(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def set_vrf(func_chain, p4_vars, vrf):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = vrf
                expr = p4_vars.set("meta.ingress_metadata.vrf", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def on_miss_2(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def on_miss_5(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def on_miss_6(func_chain, p4_vars):
            sub_chain = []

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def fib_hit_nexthop(func_chain, p4_vars, nexthop_index):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = nexthop_index
                expr = p4_vars.set("meta.ingress_metadata.nexthop_index", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVec(255, 8)
                expr = p4_vars.set("hdr.ipv4.ttl", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def fib_hit_nexthop_2(func_chain, p4_vars, nexthop_index):

            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = nexthop_index
                expr = p4_vars.set("meta.ingress_metadata.nexthop_index", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            def output_update(func_chain, p4_vars):
                rval = BitVec(255, 8)
                expr = p4_vars.set("hdr.ipv4.ttl", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def set_egress_details(func_chain, p4_vars, egress_spec):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = egress_spec
                expr = p4_vars.set("standard_metadata.egress_spec", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        def set_bd(func_chain, p4_vars, bd):
            sub_chain = []

            def output_update(func_chain, p4_vars):
                rval = bd
                expr = p4_vars.set("meta.ingress_metadata.bd", rval)
                return step(func_chain, p4_vars, expr)
            sub_chain.append(output_update)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)

        class bd_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                bd_0_key_0 = p4_vars.meta.ingress_metadata.bd
                bd_0_key_0_const = Const("bd_0_key_0", bd_0_key_0.sort())
                key_matches.append(bd_0_key_0 == bd_0_key_0_const)
                return And(key_matches)

            actions = {
                "set_vrf": (1, (set_vrf, [BitVec("bd_0_vrf", 12)])),
            }
            actions["default"] = (0, (NoAction_1, ()))

        class ipv4_fib_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                ipv4_fib_0_key_0 = p4_vars.meta.ingress_metadata.vrf
                ipv4_fib_0_key_0_const = Const(
                    "ipv4_fib_0_key_0", ipv4_fib_0_key_0.sort())
                key_matches.append(ipv4_fib_0_key_0 == ipv4_fib_0_key_0_const)

                ipv4_fib_0_key_1 = p4_vars.hdr.ipv4.dstAddr
                ipv4_fib_0_key_1_const = Const(
                    "ipv4_fib_0_key_1", ipv4_fib_0_key_1.sort())
                key_matches.append(ipv4_fib_0_key_1 == ipv4_fib_0_key_1_const)
                return And(key_matches)

            actions = {
                "on_miss_2": (1, (on_miss_2, ())),
                "fib_hit_nexthop": (2, (fib_hit_nexthop, [BitVec("ipv4_fib_0_nexthop_index", 16)])),
            }
            actions["default"] = (0, (NoAction_8, ()))

        class ipv4_fib_lpm_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                ipv4_fib_lpm_0_key_0 = p4_vars.meta.ingress_metadata.vrf
                ipv4_fib_lpm_0_key_0_const = Const(
                    "ipv4_fib_lpm_0_key_0", ipv4_fib_lpm_0_key_0.sort())
                key_matches.append(ipv4_fib_lpm_0_key_0 ==
                                   ipv4_fib_lpm_0_key_0_const)

                # This should be a mask for lpm matches
                # TODO: Make it a proper mask and fix, not sure how yet
                masks = [int("0x" + ((32 // 4) - i) * "0" +
                             i * "f", 16) for i in range(1, 32 // 4 + 1)]
                ipv4_fib_lpm_0_key_1 = p4_vars.hdr.ipv4.dstAddr
                ipv4_fib_lpm_0_key_1_const = Const(
                    "ipv4_fib_lpm_0_key_1", ipv4_fib_lpm_0_key_1.sort())
                key_matches.append(Or([ipv4_fib_lpm_0_key_1 & m ==
                                       ipv4_fib_lpm_0_key_1_const & m
                                       for m in masks]))
                return And(key_matches)

            actions = {
                "on_miss_5": (1, (on_miss_5, ())),
                "fib_hit_nexthop_2": (2, (fib_hit_nexthop_2,
                                          [BitVec("ipv4_fib_lpm_0_nexthop_index",
                                                  16)]))
            }
            actions["default"] = (0, (NoAction_9, ()))

        class nexthop_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                nexthop_0_key_0 = p4_vars.meta.ingress_metadata.nexthop_index
                nexthop_0_key_0_const = Const(
                    "nexthop_0_key_0", nexthop_0_key_0.sort())
                key_matches.append(nexthop_0_key_0 == nexthop_0_key_0_const)
                return And(key_matches)

            actions = {
                "on_miss_6": (1, (on_miss_6, ())),
                "set_egress_details": (2, (set_egress_details, [BitVec("nexthop_0_egress_spec", 9)])),
            }
            actions["default"] = (0, (NoAction_10, ()))

        class port_mapping_0(Table):

            @classmethod
            def table_match(cls, p4_vars):

                key_matches = []
                port_mapping_0_key_0 = p4_vars.standard_metadata.ingress_port
                port_mapping_0_key_0_const = Const(
                    "port_mapping_0_key_0", port_mapping_0_key_0.sort())
                key_matches.append(port_mapping_0_key_0 ==
                                   port_mapping_0_key_0_const)
                return And(key_matches)

            actions = {
                "set_bd": (1, (set_bd, [BitVec("port_mapping_0_bd", 16)])),
            }
            actions["default"] = (0, (NoAction_11, ()))

        def apply(func_chain, p4_vars):
            sub_chain = []

            def if_block(func_chain, p4_vars):

                condition = p4_vars.hdr.ipv4.isValid()

                def is_true():
                    sub_chain = []

                    sub_chain.append(port_mapping_0.apply)
                    sub_chain.append(bd_0.apply)

                    sub_chain.append(ipv4_fib_0.apply)

                    def switch_block(sub_chain, p4_vars):
                        cases = []
                        switch = ipv4_fib_0.action_run(p4_vars)
                        a = ipv4_fib_0.actions

                        def case_block(sub_chain, p4_vars):
                            sub_chain = []

                            sub_chain.append(ipv4_fib_lpm_0.apply)

                            sub_chain.extend(func_chain)
                            return step(sub_chain, p4_vars)
                        case = Implies(
                            switch == a["on_miss_2"][0],
                            case_block(func_chain, p4_vars))
                        cases.append(case)

                        default = step(func_chain, p4_vars)

                        return And(*cases, default)
                    sub_chain.append(switch_block)

                    sub_chain.extend(func_chain)
                    return step(sub_chain, p4_vars)

                def is_false():
                    sub_chain = []

                    sub_chain.extend(func_chain)
                    return step(sub_chain, p4_vars)

                return If(condition, is_true(), is_false())
            sub_chain.append(if_block)

            sub_chain.append(nexthop_0.apply)

            sub_chain.extend(func_chain)
            return step(sub_chain, p4_vars)
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
    p4_ctrl_0, p4_ctrl_0_args = p4_program_0(Z3Reg)[2]
    p4_ctrl_1, p4_ctrl_1_args = p4_program_1(Z3Reg)[2]

    # print("PROGRAM 1")
    # print(p4_ctrl_0(p4_ctrl_0_args))
    # print("PROGRAM 2")
    # print(p4_ctrl_1(p4_ctrl_1_args))
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
