from p4z3_base import *

''' Model imports at the top of the p4 file '''
from v1model import *


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


z3_args = [('ingress_metadata', z3_reg.reg["ingress_metadata_t"])]
z3_reg.register_z3_type("metadata", Struct, z3_args)


z3_args = [('ethernet', z3_reg.reg["ethernet_t"]),
           ('ipv4', z3_reg.reg["ipv4_t"])]
z3_reg.register_z3_type("headers", Struct, z3_args)


z3_args = [('hdr', z3_reg.reg["headers"]), ('meta', z3_reg.reg["metadata"]),
           ('standard_metadata', z3_reg.reg["standard_metadata_t"])]
z3_reg.register_z3_type("inouts", Struct, z3_args)


def control_ingress_0(s, inouts):
    def NoAction_1(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_8(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_9(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_10(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_11(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_vrf(func_chain, inouts, vrf):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = vrf
            expr = inouts.set("meta.ingress_metadata.vrf", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def on_miss_2(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def on_miss_5(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def on_miss_6(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def fib_hit_nexthop(func_chain, inouts, nexthop_index):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = nexthop_index
            expr = inouts.set("meta.ingress_metadata.nexthop_index", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        def output_update(func_chain, inouts):
            rval = BitVec(255, 8)
            expr = inouts.set("hdr.ipv4.ttl", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def fib_hit_nexthop_2(func_chain, inouts, nexthop_index):

        sub_chain = []

        def output_update(func_chain, inouts):
            rval = nexthop_index
            expr = inouts.set("meta.ingress_metadata.nexthop_index", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        def output_update(func_chain, inouts):
            rval = BitVec(255, 8)
            expr = inouts.set("hdr.ipv4.ttl", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_egress_details(func_chain, inouts, egress_spec):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = egress_spec
            expr = inouts.set("standard_metadata.egress_spec", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_bd(func_chain, inouts, bd):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = bd
            expr = inouts.set("meta.ingress_metadata.bd", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    class bd_0(Table):

        ma_bd_0 = Datatype('ma_bd_0')
        ma_bd_0.declare('mk_ma_bd_0', ('key_0', BitVecSort(16)),
                        ('action', IntSort()))
        ma = ma_bd_0.create()
        m = Const('bd_0_m', ma)

        actions = {
            "set_vrf": (1, (set_vrf, [BitVec("bd_0_vrf", 12)])),
        }
        actions["default"] = (0, (NoAction_1, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            bd_0_key_0 = inouts.meta.ingress_metadata.bd
            key_matches.append(bd_0_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    class ipv4_fib_0(Table):

        ma_ipv4_fib_0 = Datatype('ma_ipv4_fib_0')
        ma_ipv4_fib_0.declare('mk_ma_ipv4_fib_0', ('key_0', BitVecSort(12)), ('key_1', BitVecSort(32)),
                              ('action', IntSort()))
        ma = ma_ipv4_fib_0.create()
        m = Const('ipv4_fib_0_m', ma)

        actions = {
            "on_miss_2": (1, (on_miss_2, ())),
            "fib_hit_nexthop": (2, (fib_hit_nexthop, [BitVec("ipv4_fib_0_nexthop_index", 16)])),
        }
        actions["default"] = (0, (NoAction_8, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            ipv4_fib_0_key_0 = inouts.meta.ingress_metadata.vrf
            key_matches.append(ipv4_fib_0_key_0 == cls.ma.key_0(cls.m))
            ipv4_fib_0_key_1 = inouts.hdr.ipv4.dstAddr
            key_matches.append(ipv4_fib_0_key_1 == cls.ma.key_1(cls.m))
            return And(key_matches)

    class ipv4_fib_lpm_0(Table):

        ma_ipv4_fib_lpm_0 = Datatype('ma_ipv4_fib_lpm_0')
        ma_ipv4_fib_lpm_0.declare('mk_ma_ipv4_fib_lpm_0', ('key_0', BitVecSort(12)), ('key_1', BitVecSort(32)),
                                  ('action', IntSort()))
        ma = ma_ipv4_fib_lpm_0.create()
        m = Const('ipv4_fib_lpm_0_m', ma)

        actions = {
            "on_miss_5": (1, (on_miss_5, ())),
            "fib_hit_nexthop_2": (2, (fib_hit_nexthop_2, [BitVec("ipv4_fib_lpm_0_nexthop_index", 16)]))
        }
        actions["default"] = (0, (NoAction_9, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            ipv4_fib_lpm_0_key_0 = inouts.meta.ingress_metadata.vrf
            key_matches.append(ipv4_fib_lpm_0_key_0 == cls.ma.key_0(cls.m))

            # This should be a mask for lpm matches
            # TODO: Make it a proper mask and fix, not sure how yet
            masks = [int("0x" + ((32 // 4) - i) * "0" +
                         i * "f", 16) for i in range(1, 32 // 4 + 1)]
            ipv4_fib_lpm_0_key_1 = inouts.hdr.ipv4.dstAddr
            key_matches.append(Or([ipv4_fib_lpm_0_key_1 & m ==
                                   cls.ma.key_1(cls.m) & m
                                   for m in masks]))
            return And(key_matches)

    class nexthop_0(Table):

        ma_nexthop_0 = Datatype('ma_nexthop_0')
        ma_nexthop_0.declare('mk_ma_nexthop_0', ('key_0', BitVecSort(16)),
                             ('action', IntSort()))
        ma = ma_nexthop_0.create()
        m = Const('nexthop_0_m', ma)

        actions = {
            "on_miss_6": (1, (on_miss_6, ())),
            "set_egress_details": (2, (set_egress_details, [BitVec("nexthop_0_egress_spec", 9)])),
        }
        actions["default"] = (0, (NoAction_10, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            nexthop_0_key_0 = inouts.meta.ingress_metadata.nexthop_index
            key_matches.append(nexthop_0_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    class port_mapping_0(Table):

        ma_port_mapping_0 = Datatype('ma_port_mapping_0')
        ma_port_mapping_0.declare('mk_ma_port_mapping_0', ('key_0', BitVecSort(9)),
                                  ('action', IntSort()))
        ma = ma_port_mapping_0.create()
        m = Const('port_mapping_0_m', ma)

        actions = {
            "set_bd": (1, (set_bd, [BitVec("port_mapping_0_bd", 16)])),
        }
        actions["default"] = (0, (NoAction_11, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            port_mapping_0_key_0 = inouts.standard_metadata.ingress_port
            key_matches.append(port_mapping_0_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    def apply(func_chain, inouts):
        sub_chain = []

        def if_block(func_chain, inouts):

            condition = inouts.hdr.ipv4.isValid()

            def is_true():
                sub_chain = []

                sub_chain.append(port_mapping_0.apply)
                sub_chain.append(bd_0.apply)

                sub_chain.append(ipv4_fib_0.apply)

                def switch_block(sub_chain, inouts):
                    cases = []
                    switch = ipv4_fib_0.action_run(inouts)
                    a = ipv4_fib_0.actions

                    def case_block(sub_chain, inouts):
                        sub_chain = []

                        sub_chain.append(ipv4_fib_lpm_0.apply)

                        sub_chain.extend(func_chain)
                        return step(sub_chain, inouts)
                    case = Implies(
                        switch == a["on_miss_2"][0],
                        case_block(func_chain, inouts))
                    cases.append(case)

                    default = step(func_chain, inouts)

                    return And(*cases, default)
                sub_chain.append(switch_block)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)

            def is_false():
                sub_chain = []

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)

            return If(condition, is_true(), is_false())
        sub_chain.append(if_block)

        sub_chain.append(nexthop_0.apply)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)
    # return the apply function as sequence of logic clauses
    return step(func_chain=[apply], inouts=inouts)


def control_ingress_1(s, inouts):
    ''' This is the initial version of the program. '''

    def NoAction_1(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_8(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_9(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_10(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def NoAction_11(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_vrf(func_chain, inouts, vrf):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = vrf
            expr = inouts.set("meta.ingress_metadata.vrf", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def on_miss_2(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def on_miss_5(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def on_miss_6(func_chain, inouts):
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def fib_hit_nexthop(func_chain, inouts, nexthop_index):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = nexthop_index
            expr = inouts.set("meta.ingress_metadata.nexthop_index", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        def output_update(func_chain, inouts):
            rval = BitVec(255, 8)
            expr = inouts.set("hdr.ipv4.ttl", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def fib_hit_nexthop_2(func_chain, inouts, nexthop_index):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = nexthop_index
            expr = inouts.set("meta.ingress_metadata.nexthop_index", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        def output_update(func_chain, inouts):
            rval = BitVec(255, 8)
            expr = inouts.set("hdr.ipv4.ttl", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_egress_details(func_chain, inouts, egress_spec):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = egress_spec
            expr = inouts.set("standard_metadata.egress_spec", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_bd(func_chain, inouts, bd):
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = bd
            expr = inouts.set("meta.ingress_metadata.bd", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    class bd_0(Table):

        ma_bd_0 = Datatype('ma_bd_0')
        ma_bd_0.declare('mk_ma_bd_0', ('key_0', BitVecSort(16)),
                        ('action', IntSort()))
        ma = ma_bd_0.create()
        m = Const('bd_0_m', ma)

        actions = {
            "set_vrf": (1, (set_vrf, [BitVec("bd_0_vrf", 12)])),
        }
        actions["default"] = (0, (NoAction_1, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            bd_0_key_0 = inouts.meta.ingress_metadata.bd
            key_matches.append(bd_0_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    class ipv4_fib_0(Table):

        ma_ipv4_fib_0 = Datatype('ma_ipv4_fib_0')
        ma_ipv4_fib_0.declare('mk_ma_ipv4_fib_0', ('key_0', BitVecSort(12)), ('key_1', BitVecSort(32)),
                              ('action', IntSort()))
        ma = ma_ipv4_fib_0.create()
        m = Const('ipv4_fib_0_m', ma)

        actions = {
            "on_miss_2": (1, (on_miss_2, ())),
            "fib_hit_nexthop": (2, (fib_hit_nexthop, [BitVec("ipv4_fib_0_nexthop_index", 16)])),
        }
        actions["default"] = (0, (NoAction_8, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            ipv4_fib_0_key_0 = inouts.meta.ingress_metadata.vrf
            key_matches.append(ipv4_fib_0_key_0 == cls.ma.key_0(cls.m))
            ipv4_fib_0_key_1 = inouts.hdr.ipv4.dstAddr
            key_matches.append(ipv4_fib_0_key_1 == cls.ma.key_1(cls.m))
            return And(key_matches)

    class ipv4_fib_lpm_0(Table):

        ma_ipv4_fib_lpm_0 = Datatype('ma_ipv4_fib_lpm_0')
        ma_ipv4_fib_lpm_0.declare('mk_ma_ipv4_fib_lpm_0', ('key_0', BitVecSort(12)), ('key_1', BitVecSort(32)),
                                  ('action', IntSort()))
        ma = ma_ipv4_fib_lpm_0.create()
        m = Const('ipv4_fib_lpm_0_m', ma)

        actions = {
            "on_miss_5": (1, (on_miss_5, ())),
            "fib_hit_nexthop_2": (2, (fib_hit_nexthop_2, [BitVec("ipv4_fib_lpm_0_nexthop_index", 16)]))
        }
        actions["default"] = (0, (NoAction_9, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            ipv4_fib_lpm_0_key_0 = inouts.meta.ingress_metadata.vrf
            key_matches.append(ipv4_fib_lpm_0_key_0 == cls.ma.key_0(cls.m))

            # This should be a mask for lpm matches
            # TODO: Make it a proper mask and fix
            masks = [int("0x" + ((32 // 4) - i) * "0" +
                         i * "f", 16) for i in range(1, 32 // 4 + 1)]
            ipv4_fib_lpm_0_key_1 = inouts.hdr.ipv4.dstAddr
            key_matches.append(Or([(ipv4_fib_lpm_0_key_1 & m) ==
                                   (cls.ma.key_1(cls.m) & m)
                                   for m in masks]))
            return And(key_matches)

    class nexthop_0(Table):

        ma_nexthop_0 = Datatype('ma_nexthop_0')
        ma_nexthop_0.declare('mk_ma_nexthop_0', ('key_0', BitVecSort(16)),
                             ('action', IntSort()))
        ma = ma_nexthop_0.create()
        m = Const('nexthop_0_m', ma)

        actions = {
            "on_miss_6": (1, (on_miss_6, ())),
            "set_egress_details": (2, (set_egress_details, [BitVec("nexthop_0_egress_spec", 9)])),
        }
        actions["default"] = (0, (NoAction_10, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            nexthop_0_key_0 = inouts.meta.ingress_metadata.nexthop_index
            key_matches.append(nexthop_0_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    class port_mapping_0(Table):

        ma_port_mapping_0 = Datatype('ma_port_mapping_0')
        ma_port_mapping_0.declare('mk_ma_port_mapping_0', ('key_0', BitVecSort(9)),
                                  ('action', IntSort()))
        ma = ma_port_mapping_0.create()
        m = Const('port_mapping_0_m', ma)

        actions = {
            "set_bd": (1, (set_bd, [BitVec("port_mapping_0_bd", 16)])),
        }
        actions["default"] = (0, (NoAction_11, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            port_mapping_0_key_0 = inouts.standard_metadata.ingress_port
            key_matches.append(port_mapping_0_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    def apply(func_chain, inouts):
        sub_chain = []

        def if_block(func_chain, inouts):

            condition = inouts.hdr.ipv4.isValid()

            def is_true():
                sub_chain = []

                sub_chain.append(port_mapping_0.apply)
                sub_chain.append(bd_0.apply)

                sub_chain.append(ipv4_fib_0.apply)

                def switch_block(sub_chain, inouts):
                    cases = []
                    switch = ipv4_fib_0.action_run(inouts)
                    a = ipv4_fib_0.actions

                    def case_block(sub_chain, inouts):
                        sub_chain = []

                        sub_chain.append(ipv4_fib_lpm_0.apply)

                        sub_chain.extend(func_chain)
                        return step(sub_chain, inouts)
                    case = Implies(
                        switch == a["on_miss_2"][0],
                        case_block(func_chain, inouts))
                    cases.append(case)
                    default = step(func_chain, inouts)

                    return And(*cases, default)
                sub_chain.append(switch_block)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)

            def is_false():
                sub_chain = []

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)

            return If(condition, is_true(), is_false())
        sub_chain.append(if_block)

        sub_chain.append(nexthop_0.apply)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)
    return step(func_chain=[apply], inouts=inouts)


def z3_check():

    s = Solver()

    inouts = z3_reg.reg["INOUTS"]()
    bounds = [inouts.const]
    # out = control_ingress_0(s, inouts)
    # print("FINAL OUTPUT")
    # print(out)
    # exit(0)
    tv_equiv = simplify(control_ingress_0(s, inouts) !=
                        control_ingress_1(s, inouts))
    s.add(Exists(bounds, tv_equiv))
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
