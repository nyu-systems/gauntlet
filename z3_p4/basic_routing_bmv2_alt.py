from p4z3_expressions import *


def p4_program_0(z3_reg):
    ''' HEADERS '''
    # The input headers of the control pipeline
    # Model imports at the top of the p4 file '''
    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
        ('vrf', BitVecSort(12)),
        ('bd', BitVecSort(16)),
        ('nexthop_index', BitVecSort(16))
    ]

    z3_reg.register_z3_type("ingress_metadata_t", Struct, z3_args)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('version', BitVecSort(4)), ('ihl', BitVecSort(4)),
               ('diffserv', BitVecSort(8)), ('totalLen', BitVecSort(16)),
               ('identification', BitVecSort(16)), ('flags', BitVecSort(3)),
               ('fragOffset', BitVecSort(13)), ('ttl', BitVecSort(8)),
               ('protocol', BitVecSort(8)), ('hdrChecksum', BitVecSort(16)),
               ('srcAddr', BitVecSort(32)), ('dstAddr', BitVecSort(32))
               ]
    z3_reg.register_z3_type("ipv4_t", Header, z3_args)

    z3_args = [('ingress_metadata', z3_reg.types["ingress_metadata_t"])]
    z3_reg.register_z3_type("metadata", Struct, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"]),
               ('ipv4', z3_reg.types["ipv4_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["metadata"]),
               ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

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

        def NoAction_1(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def NoAction_8(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def NoAction_9(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def NoAction_10(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def NoAction_11(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def set_vrf(p4_vars, expr_chain, vrf):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "meta.ingress_metadata.vrf"
                rval = vrf
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def on_miss_2(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def on_miss_5(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def on_miss_6(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def fib_hit_nexthop(p4_vars, expr_chain, nexthop_index):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "meta.ingress_metadata.nexthop_index"
                rval = nexthop_index
                assign.add_assign(lval, rval)
                block.add(assign)

                assign = AssignmentStatement()
                lval = "hdr.ipv4.ttl"
                rval = BitVec(255, 8)
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def fib_hit_nexthop_2(p4_vars, expr_chain, nexthop_index):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "meta.ingress_metadata.nexthop_index"
                rval = nexthop_index
                assign.add_assign(lval, rval)
                block.add(assign)

                assign = AssignmentStatement()
                lval = "hdr.ipv4.ttl"
                rval = BitVec(255, 8)
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def set_egress_details(p4_vars, expr_chain, egress_spec):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "standard_metadata.egress_spec"
                rval = egress_spec
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def set_bd(p4_vars, expr_chain, bd):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "meta.ingress_metadata.bd"
                rval = bd
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        bd_0 = TableExpr("bd_0")
        bd_0.add_action("set_vrf", set_vrf, BitVec("bd_0_vrf", 12))
        bd_0.add_default(NoAction_1,)

        def table_key(p4_vars): return p4_vars.meta.ingress_metadata.bd
        bd_0.add_match(table_key)

        ipv4_fib_0 = TableExpr("ipv4_fib_0")
        ipv4_fib_0.add_action("on_miss_2", on_miss_2, )
        ipv4_fib_0.add_action("fib_hit_nexthop", fib_hit_nexthop,
                              BitVec("ipv4_fib_0_nexthop_index", 16))
        ipv4_fib_0.add_default(NoAction_8,)

        def table_key(p4_vars): return p4_vars.meta.ingress_metadata.vrf
        ipv4_fib_0.add_match(table_key)

        def table_key(p4_vars): return p4_vars.hdr.ipv4.dstAddr
        ipv4_fib_0.add_match(table_key)

        ipv4_fib_lpm_0 = TableExpr("ipv4_fib_lpm_0")
        ipv4_fib_lpm_0.add_action("on_miss_5", on_miss_5, )
        ipv4_fib_lpm_0.add_action("fib_hit_nexthop_2", fib_hit_nexthop_2,
                                  BitVec("ipv4_fib_lpm_0_nexthop_index", 16))
        ipv4_fib_lpm_0.add_default(NoAction_9,)

        def table_key(p4_vars): return p4_vars.meta.ingress_metadata.vrf
        ipv4_fib_lpm_0.add_match(table_key)
        # TODO UPDATE TO LPM

        def table_key(p4_vars): return p4_vars.hdr.ipv4.srcAddr
        ipv4_fib_lpm_0.add_match(table_key)

        nexthop_0 = TableExpr("nexthop_0")
        ipv4_fib_lpm_0.add_action("on_miss_6", on_miss_6, )
        nexthop_0.add_action("set_egress_details", set_egress_details,
                             BitVec("nexthop_0_egress_spec", 9))
        nexthop_0.add_default(NoAction_10,)

        def table_key(
            p4_vars): return p4_vars.meta.ingress_metadata.nexthop_index
        nexthop_0.add_match(table_key)

        port_mapping_0 = TableExpr("port_mapping_0")
        port_mapping_0.add_action(
            "set_bd", set_bd, BitVec("port_mapping_0_bd", 16))
        port_mapping_0.add_default(NoAction_11,)

        def table_key(p4_vars): return p4_vars.standard_metadata.ingress_port
        port_mapping_0.add_match(table_key)

        def BLOCK():
            block = BlockStatement()

            if_block = IfStatement()
            condition = p4_vars.hdr.ipv4.isValid()
            if_block.add_condition(condition)
            if_block.add_then_stmt(port_mapping_0.apply())
            if_block.add_then_stmt(bd_0.apply())

            switch_block = SwitchStatement(ipv4_fib_0)
            switch_block.add_case("on_miss_2")
            switch_block.add_stmt_to_case("on_miss_2", ipv4_fib_lpm_0.apply())
            if_block.add_then_stmt(switch_block)
            if_block.add_then_stmt(nexthop_0.apply())
            block.add(if_block)
            return block

        return BLOCK().eval(p4_vars)

    return ((p,), (vrfy,), (ingress, ingress_args), (egress,), (update,), (deparser,))


def p4_program_1(z3_reg):
    ''' HEADERS '''
    # The input headers of the control pipeline
    # Model imports at the top of the p4 file '''
    import v1model
    z3_reg = v1model.register(z3_reg)

    z3_args = [
        ('vrf', BitVecSort(12)),
        ('bd', BitVecSort(16)),
        ('nexthop_index', BitVecSort(16))
    ]

    z3_reg.register_z3_type("ingress_metadata_t", Struct, z3_args)

    z3_args = [
        ('dstAddr', BitVecSort(48)),
        ('srcAddr', BitVecSort(48)),
        ('etherType', BitVecSort(16))]

    z3_reg.register_z3_type("ethernet_t", Header, z3_args)

    z3_args = [('version', BitVecSort(4)), ('ihl', BitVecSort(4)),
               ('diffserv', BitVecSort(8)), ('totalLen', BitVecSort(16)),
               ('identification', BitVecSort(16)), ('flags', BitVecSort(3)),
               ('fragOffset', BitVecSort(13)), ('ttl', BitVecSort(8)),
               ('protocol', BitVecSort(8)), ('hdrChecksum', BitVecSort(16)),
               ('srcAddr', BitVecSort(32)), ('dstAddr', BitVecSort(32))
               ]
    z3_reg.register_z3_type("ipv4_t", Header, z3_args)

    z3_args = [('ingress_metadata', z3_reg.types["ingress_metadata_t"])]
    z3_reg.register_z3_type("metadata", Struct, z3_args)

    z3_args = [('ethernet', z3_reg.types["ethernet_t"]),
               ('ipv4', z3_reg.types["ipv4_t"])]
    z3_reg.register_z3_type("headers", Struct, z3_args)

    z3_args = [('hdr', z3_reg.types["headers"]), ('meta', z3_reg.types["metadata"]),
               ('standard_metadata', z3_reg.types["standard_metadata_t"])]
    z3_reg.register_z3_type("inouts", P4State, z3_args)
    ingress_args = z3_reg.instance("inouts")

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

        def NoAction_1(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def NoAction_8(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def NoAction_9(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def NoAction_10(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def NoAction_11(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def set_vrf(p4_vars, expr_chain, vrf):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "meta.ingress_metadata.vrf"
                rval = vrf
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def on_miss_2(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def on_miss_5(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def on_miss_6(p4_vars, expr_chain):
            def BLOCK():
                block = BlockStatement()
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def fib_hit_nexthop(p4_vars, expr_chain, nexthop_index):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "meta.ingress_metadata.nexthop_index"
                rval = nexthop_index
                assign.add_assign(lval, rval)
                block.add(assign)

                assign = AssignmentStatement()
                lval = "hdr.ipv4.ttl"
                rval = BitVec(255, 8)
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def fib_hit_nexthop_2(p4_vars, expr_chain, nexthop_index):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "meta.ingress_metadata.nexthop_index"
                rval = nexthop_index
                assign.add_assign(lval, rval)
                block.add(assign)

                assign = AssignmentStatement()
                lval = "hdr.ipv4.ttl"
                rval = BitVec(255, 8)
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def set_egress_details(p4_vars, expr_chain, egress_spec):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "standard_metadata.egress_spec"
                rval = egress_spec
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        def set_bd(p4_vars, expr_chain, bd):
            def BLOCK():
                block = BlockStatement()
                assign = AssignmentStatement()
                lval = "meta.ingress_metadata.bd"
                rval = bd
                assign.add_assign(lval, rval)
                block.add(assign)
                return block
            return BLOCK().eval(p4_vars, expr_chain)

        bd_0 = TableExpr("bd_0")
        bd_0.add_action("set_vrf", set_vrf, BitVec("bd_0_vrf", 12))
        bd_0.add_default(NoAction_1,)

        def table_key(p4_vars): return p4_vars.meta.ingress_metadata.bd
        bd_0.add_match(table_key)

        ipv4_fib_0 = TableExpr("ipv4_fib_0")
        ipv4_fib_0.add_action("on_miss_2", on_miss_2, )
        ipv4_fib_0.add_action("fib_hit_nexthop", fib_hit_nexthop,
                              BitVec("ipv4_fib_0_nexthop_index", 16))
        ipv4_fib_0.add_default(NoAction_8,)

        def table_key(p4_vars): return p4_vars.meta.ingress_metadata.vrf
        ipv4_fib_0.add_match(table_key)

        def table_key(p4_vars): return p4_vars.hdr.ipv4.dstAddr
        ipv4_fib_0.add_match(table_key)

        ipv4_fib_lpm_0 = TableExpr("ipv4_fib_lpm_0")
        ipv4_fib_lpm_0.add_action("on_miss_5", on_miss_5, )
        ipv4_fib_lpm_0.add_action("fib_hit_nexthop_2", fib_hit_nexthop_2,
                                  BitVec("ipv4_fib_lpm_0_nexthop_index", 16))
        ipv4_fib_lpm_0.add_default(NoAction_9,)

        def table_key(p4_vars): return p4_vars.meta.ingress_metadata.vrf
        ipv4_fib_lpm_0.add_match(table_key)
        # TODO UPDATE TO LPM

        def table_key(p4_vars): return p4_vars.hdr.ipv4.srcAddr
        ipv4_fib_lpm_0.add_match(table_key)

        nexthop_0 = TableExpr("nexthop_0")
        ipv4_fib_lpm_0.add_action("on_miss_6", on_miss_6, )
        nexthop_0.add_action("set_egress_details", set_egress_details,
                             BitVec("nexthop_0_egress_spec", 9))
        nexthop_0.add_default(NoAction_10,)

        def table_key(
            p4_vars): return p4_vars.meta.ingress_metadata.nexthop_index
        nexthop_0.add_match(table_key)

        port_mapping_0 = TableExpr("port_mapping_0")
        port_mapping_0.add_action(
            "set_bd", set_bd, BitVec("port_mapping_0_bd", 16))
        port_mapping_0.add_default(NoAction_11,)

        def table_key(p4_vars): return p4_vars.standard_metadata.ingress_port
        port_mapping_0.add_match(table_key)

        def BLOCK():
            block = BlockStatement()

            if_block = IfStatement()
            condition = p4_vars.hdr.ipv4.isValid()
            if_block.add_condition(condition)
            if_block.add_then_stmt(port_mapping_0.apply())
            if_block.add_then_stmt(bd_0.apply())

            switch_block = SwitchStatement(ipv4_fib_0)
            switch_block.add_case("on_miss_2")
            switch_block.add_stmt_to_case("on_miss_2", ipv4_fib_lpm_0.apply())
            if_block.add_then_stmt(switch_block)
            if_block.add_then_stmt(nexthop_0.apply())
            block.add(if_block)
            return block

        return BLOCK().eval(p4_vars)

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
    print("SMT2 EXPRESSION")
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
