# (declare-const key (_ BitVec 32))
# (declare-datatypes () ((H (mk-h (a (_ BitVec 32)) (b (_ BitVec 32)) ))))
# (declare-const h H)
# (define-fun pass_0 ((h H)) (H)
#     (ite (= (bvadd (a h) (a h)) key) (mk-h (a h) (a h)) (mk-h (a h) (b h)) )
# )
# (define-const key_0 (_ BitVec 32) (bvadd (a h) (a h)))
# (define-fun pass_1 ((h H)) (H)
#     (ite (= key_0 key)  (mk-h (a h) (a h)) (mk-h (a h) (b h)) )
# )
# (assert (not ( = (pass_0 h) (pass_1 h))))
# (check-sat)


from z3 import *

# declaration of the global header type that is to be parsed
ethernet_t = Datatype('ethernet_t')
ethernet_t.declare('mk_ethernet_t',
                   ('dstAddr', BitVecSort(48)),
                   ('srcAddr', BitVecSort(48)),
                   ('etherType', BitVecSort(16)))
ethernet_t = ethernet_t.create()

ipv4_t = Datatype('ipv4_t')
ipv4_t.declare('mk_ipv4_t',
               ('version', BitVecSort(4)), ('ihl', BitVecSort(4)),
               ('diffserv', BitVecSort(8)), ('totalLen', BitVecSort(16)),
               ('identification', BitVecSort(16)), ('flags', BitVecSort(3)),
               ('fragOffset', BitVecSort(13)), ('ttl', BitVecSort(8)),
               ('protocol', BitVecSort(8)), ('hdrChecksum', BitVecSort(16)),
               ('srcAddr', BitVecSort(32)), ('dstAddr', BitVecSort(32)))
ipv4_t = ipv4_t.create()

ingress_metadata_t = Datatype('ingress_metadata_t')
ingress_metadata_t.declare('mk_ingress_metadata_t',
                           ('vrf', BitVecSort(12)), ('bd', BitVecSort(16)),
                           ('nexthop_index', BitVecSort(16)))
ingress_metadata_t = ingress_metadata_t.create()

# the final output in a single datatype
output = Datatype('p4_output')
output.declare('mk_output',
               ('ethernet_t', ethernet_t), ('ipv4_t', ipv4_t),
               ('ingress_metadata_t', ingress_metadata_t),
               ('egress_spec', BitVecSort(9)))
output = output.create()

# the table constant we are matching with
ma_bd_0 = Datatype('ma_bd_0')
ma_bd_0.declare('mk_ma_bd_0', ('key_0', BitVecSort(16)), ('action', IntSort()))
ma_bd_0 = ma_bd_0.create()

ma_ipv4_fib_0 = Datatype('ma_ipv4_fib_0')
ma_ipv4_fib_0.declare('mk_ma_ipv4_fib_0',
                      ('key_0', BitVecSort(12)),
                      ('key_1', BitVecSort(32)),
                      ('action', IntSort()))
ma_ipv4_fib_0 = ma_ipv4_fib_0.create()

ma_ipv4_fib_lpm_0 = Datatype('ma_ipv4_fib_lpm_0')
ma_ipv4_fib_lpm_0.declare('mk_ma_ipv4_fib_lpm_0',
                          ('key_0', BitVecSort(12)),
                          ('key_1', BitVecSort(32)),
                          ('action', IntSort()))
ma_ipv4_fib_lpm_0 = ma_ipv4_fib_lpm_0.create()

ma_nexthop_0 = Datatype('ma_nexthop_0')
ma_nexthop_0.declare(
    'mk_ma_nexthop_0', ('key_0', BitVecSort(16)), ('action', IntSort()))
ma_nexthop_0 = ma_nexthop_0.create()

ma_port_mapping_0 = Datatype('ma_port_mapping_0')
ma_port_mapping_0.declare('mk_ma_port_mapping_0',
                          ('key_0', BitVecSort(16)), ('action', IntSort()))
ma_port_mapping_0 = ma_port_mapping_0.create()


# TODO: Add some better notion of egress spec

# define the headers...
ethernet = Const('ethernet', ethernet_t)
ethernet_valid = Const('ethernet_valid', BoolSort())
ipv4 = Const('ipv4', ipv4_t)
ipv4_valid = Const('ipv4_valid', BoolSort())
ingress_metadata = Const('ingress_metadata', ingress_metadata_t)

# and match-action entries
bd_0_m = Const('bd_0_m', ma_bd_0)
ipv4_fib_0_m = Const('ipv4_fib_0_m', ma_ipv4_fib_0)
ipv4_fib_lpm_0_m = Const('ipv4_fib_lpm_0_m', ma_ipv4_fib_lpm_0)
nexthop_0_m = Const('nexthop_0_m', ma_nexthop_0)
port_mapping_0_m = Const('port_mapping_0_m', ma_port_mapping_0)


s = Solver()

# non-modifiable input variable
ingress_port = BitVec("ingress_port", 16)


def control_ingress_0():
    # This is the initial version of the program

    # initialize new variables
    egress_spec = BitVecVal(0, 9)

    # modifiable variables
    ethernet_ret = ethernet
    ipv4_ret = ipv4
    ingress_metadata_ret = ingress_metadata

    def NoAction_1():
        return 1

    def NoAction_8():
        return 2

    def NoAction_9():
        return 3

    def NoAction_10():
        return 4

    def NoAction_11():
        return 5

    def set_vrf(vrf_arg):
        nonlocal ingress_metadata_ret
        ingress_metadata_ret = ingress_metadata_t.mk_ingress_metadata_t(
            vrf_arg,
            ingress_metadata_t.bd(ingress_metadata_ret),
            ingress_metadata_t.nexthop_index(ingress_metadata_ret))
        return 6

    def on_miss_2():
        return 7

    def on_miss_5():
        return 8

    def on_miss_6():
        return 9

    def fib_hit_nexthop(nexthop_index_arg):
        nonlocal ingress_metadata_ret
        ingress_metadata_ret = ingress_metadata_t.mk_ingress_metadata_t(
            ingress_metadata_t.vrf(ingress_metadata_ret),
            ingress_metadata_t.bd(ingress_metadata_ret),
            nexthop_index_arg)
        nonlocal ipv4_ret
        ipv4_ret = ipv4_t.mk_ipv4_t(
            ipv4_t.version(ipv4_ret), ipv4_t.ihl(ipv4_ret),
            ipv4_t.diffserv(ipv4_ret), ipv4_t.totalLen(ipv4_ret),
            ipv4_t.identification(ipv4_ret), ipv4_t.flags(ipv4_ret),
            ipv4_t.fragOffset(ipv4_ret), ipv4_t.ttl(
                ipv4_ret) + BitVecVal(255, 8),
            ipv4_t.protocol(ipv4_ret), ipv4_t.hdrChecksum(ipv4_ret),
            ipv4_t.srcAddr(ipv4_ret), ipv4_t.dstAddr(ipv4_ret))
        return 10

    def fib_hit_nexthop_2(nexthop_index_arg):
        nonlocal ingress_metadata_ret
        ingress_metadata_ret = ingress_metadata_t.mk_ingress_metadata_t(
            ingress_metadata_t.vrf(ingress_metadata_ret),
            ingress_metadata_t.bd(ingress_metadata_ret),
            nexthop_index_arg)
        nonlocal ipv4_ret
        ipv4_ret = ipv4_t.mk_ipv4_t(
            ipv4_t.version(ipv4_ret), ipv4_t.ihl(ipv4_ret),
            ipv4_t.diffserv(ipv4_ret), ipv4_t.totalLen(ipv4_ret),
            ipv4_t.identification(ipv4_ret), ipv4_t.flags(ipv4_ret),
            ipv4_t.fragOffset(ipv4_ret), ipv4_t.ttl(
                ipv4_ret) + BitVecVal(255, 8),
            ipv4_t.protocol(ipv4_ret), ipv4_t.hdrChecksum(ipv4_ret),
            ipv4_t.srcAddr(ipv4_ret), ipv4_t.dstAddr(ipv4_ret))
        return 11

    def set_egress_details(egress_spec_arg):
        nonlocal egress_spec
        egress_spec = egress_spec_arg
        return 12

    def set_bd(bd_arg):
        nonlocal ingress_metadata_ret
        ingress_metadata_ret = ingress_metadata_t.mk_ingress_metadata_t(
            ingress_metadata_t.vrf(ingress_metadata_ret),
            bd_arg,
            ingress_metadata_t.nexthop_index(ingress_metadata_ret))
        return 13

    def bd_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_bd_0.action(bd_0_m), ma_bd_0.action(bd_0_m) < 2)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_1()

        def select_action():
            return If(ma_bd_0.action(bd_0_m) == 1,
                      set_vrf(BitVec("vrf_arg", 12)),
                      # this should be an abort of some form
                      0
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.bd(ingress_metadata)
        return If(key_0 == ma_bd_0.key_0(bd_0_m),
                  select_action(), default())

    def ipv4_fib_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_ipv4_fib_0.action(ipv4_fib_0_m),
              ma_ipv4_fib_0.action(ipv4_fib_0_m) < 3)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_8()

        def select_action():
            return If(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1,
                      on_miss_2(),
                      (If(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 2,
                          fib_hit_nexthop(BitVec("nexthop_index_arg", 16)),
                          # this should be an abort of some form
                          0
                          ))
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.vrf(ingress_metadata)
        key_1 = ipv4_t.dstAddr(ipv4)
        return If(And(key_0 == ma_ipv4_fib_0.key_0(ipv4_fib_0_m),
                      key_1 == ma_ipv4_fib_0.key_1(ipv4_fib_0_m)),
                  select_action(), default())

    def ipv4_fib_lpm_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m),
              ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) < 3)
        # This should be a mask for lpm matches
        # TODO: Make it a proper mask and fix
        masks = [(2**i) - 1 for i in range(32)]

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_9()

        def select_action():
            return If(ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 1,
                      on_miss_5(),
                      (If(ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 2,
                          fib_hit_nexthop_2(BitVec("nexthop_index_arg", 16)),
                          # this should be an abort of some form
                          0
                          ))
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.vrf(ingress_metadata)
        key_1 = ipv4_t.dstAddr(ipv4)
        return If(And(key_0 == ma_ipv4_fib_lpm_0.key_0(ipv4_fib_lpm_0_m),
                      Or([key_1 & m ==
                          ma_ipv4_fib_lpm_0.key_1(ipv4_fib_lpm_0_m) & m
                          for m in masks])),
                  select_action(), default())

    def nexthop_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_nexthop_0.action(nexthop_0_m),
              ma_nexthop_0.action(nexthop_0_m) < 3)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_10()

        def select_action():
            return If(ma_nexthop_0.action(nexthop_0_m) == 1,
                      on_miss_6(),
                      If(ma_nexthop_0.action(nexthop_0_m) == 2,
                          set_egress_details(BitVec("egress_spec_arg", 9)),
                          # this should be an abort of some form
                          0
                         )
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.nexthop_index(ingress_metadata)
        return If(key_0 == ma_nexthop_0.key_0(nexthop_0_m),
                  select_action(), default())

    def port_mapping_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_port_mapping_0.action(port_mapping_0_m),
              ma_port_mapping_0.action(port_mapping_0_m) < 2)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_11()

        def select_action():
            return If(ma_port_mapping_0.action(port_mapping_0_m) == 1,
                      set_bd(BitVec("bd_arg", 16)), 0)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_port
        return If(key_0 == ma_port_mapping_0.key_0(port_mapping_0_m),
                  select_action(), default())

    port_mapping_0()
    bd_0()
    ipv4_fib_0()
    ipv4_fib_lpm_0()
    nexthop_0()
    # begin apply
    # skip valid for now
    # this is intended to express the switch case statement
    # If(ipv4_fib_0() == 7, ipv4_fib_lpm_0(), 0)
    # If(ipv4_valid, p4_apply(), Var(False, BoolSort()))
    return output.mk_output(ethernet_ret, ipv4_ret, ingress_metadata_ret, egress_spec)


def control_ingress_1():
    # This is the initial version of the program

    # initialize new variables
    egress_spec = BitVecVal(0, 9)

    # modifiable variables
    ethernet_ret = ethernet
    ipv4_ret = ipv4
    ingress_metadata_ret = ingress_metadata

    def NoAction_1():
        return 1

    def NoAction_8():
        return 2

    def NoAction_9():
        return 3

    def NoAction_10():
        return 4

    def NoAction_11():
        return 5

    def set_vrf(vrf_arg):
        nonlocal ingress_metadata_ret
        ingress_metadata_ret = ingress_metadata_t.mk_ingress_metadata_t(
            vrf_arg,
            ingress_metadata_t.bd(ingress_metadata_ret),
            ingress_metadata_t.nexthop_index(ingress_metadata_ret))
        return 6

    def on_miss_2():
        return 7

    def on_miss_5():
        return 8

    def on_miss_6():
        return 9

    def fib_hit_nexthop(nexthop_index_arg):
        nonlocal ingress_metadata_ret
        ingress_metadata_ret = ingress_metadata_t.mk_ingress_metadata_t(
            ingress_metadata_t.vrf(ingress_metadata_ret),
            ingress_metadata_t.bd(ingress_metadata_ret),
            nexthop_index_arg)
        nonlocal ipv4_ret
        ipv4_ret = ipv4_t.mk_ipv4_t(
            ipv4_t.version(ipv4_ret), ipv4_t.ihl(ipv4_ret),
            ipv4_t.diffserv(ipv4_ret), ipv4_t.totalLen(ipv4_ret),
            ipv4_t.identification(ipv4_ret), ipv4_t.flags(ipv4_ret),
            ipv4_t.fragOffset(ipv4_ret), ipv4_t.ttl(
                ipv4_ret) + BitVecVal(255, 8),
            ipv4_t.protocol(ipv4_ret), ipv4_t.hdrChecksum(ipv4_ret),
            ipv4_t.srcAddr(ipv4_ret), ipv4_t.dstAddr(ipv4_ret))
        return 10

    def fib_hit_nexthop_2(nexthop_index_arg):
        nonlocal ingress_metadata_ret
        ingress_metadata_ret = ingress_metadata_t.mk_ingress_metadata_t(
            ingress_metadata_t.vrf(ingress_metadata_ret),
            ingress_metadata_t.bd(ingress_metadata_ret),
            nexthop_index_arg)
        nonlocal ipv4_ret
        ipv4_ret = ipv4_t.mk_ipv4_t(
            ipv4_t.version(ipv4_ret), ipv4_t.ihl(ipv4_ret),
            ipv4_t.diffserv(ipv4_ret), ipv4_t.totalLen(ipv4_ret),
            ipv4_t.identification(ipv4_ret), ipv4_t.flags(ipv4_ret),
            ipv4_t.fragOffset(ipv4_ret), ipv4_t.ttl(
                ipv4_ret) + BitVecVal(255, 8),
            ipv4_t.protocol(ipv4_ret), ipv4_t.hdrChecksum(ipv4_ret),
            ipv4_t.srcAddr(ipv4_ret), ipv4_t.dstAddr(ipv4_ret))
        return 11

    def set_egress_details(egress_spec_arg):
        nonlocal egress_spec
        egress_spec = egress_spec_arg
        return 12

    def set_bd(bd_arg):
        nonlocal ingress_metadata_ret
        ingress_metadata_ret = ingress_metadata_t.mk_ingress_metadata_t(
            ingress_metadata_t.vrf(ingress_metadata_ret),
            bd_arg,
            ingress_metadata_t.nexthop_index(ingress_metadata_ret))
        return 13

    def bd_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_bd_0.action(bd_0_m), ma_bd_0.action(bd_0_m) < 2)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_1()

        def select_action():
            return If(ma_bd_0.action(bd_0_m) == 1,
                      set_vrf(BitVec("vrf_arg", 12)),
                      # this should be an abort of some form
                      0
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.bd(ingress_metadata)
        return If(key_0 == ma_bd_0.key_0(bd_0_m),
                  select_action(), default())

    def ipv4_fib_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_ipv4_fib_0.action(ipv4_fib_0_m),
              ma_ipv4_fib_0.action(ipv4_fib_0_m) < 3)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_8()

        def select_action():
            return If(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1,
                      on_miss_2(),
                      (If(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 2,
                          fib_hit_nexthop(BitVec("nexthop_index_arg", 16)),
                          # this should be an abort of some form
                          0
                          ))
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.vrf(ingress_metadata)
        key_1 = ipv4_t.dstAddr(ipv4)
        return If(And(key_0 == ma_ipv4_fib_0.key_0(ipv4_fib_0_m),
                      key_1 == ma_ipv4_fib_0.key_1(ipv4_fib_0_m)),
                  select_action(), default())

    def ipv4_fib_lpm_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m),
              ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) < 3)
        # This should be a mask for lpm matches
        # TODO: Make it a proper mask and fix
        masks = [(2**i) - 1 for i in range(32)]

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_9()

        def select_action():
            return If(ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 1,
                      on_miss_5(),
                      (If(ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 2,
                          fib_hit_nexthop_2(BitVec("nexthop_index_arg", 16)),
                          # this should be an abort of some form
                          0
                          ))
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.vrf(ingress_metadata)
        key_1 = ipv4_t.dstAddr(ipv4)
        return If(And(key_0 == ma_ipv4_fib_lpm_0.key_0(ipv4_fib_lpm_0_m),
                      Or([key_1 & m ==
                          ma_ipv4_fib_lpm_0.key_1(ipv4_fib_lpm_0_m) & m
                          for m in masks])),
                  select_action(), default())

    def nexthop_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_nexthop_0.action(nexthop_0_m),
              ma_nexthop_0.action(nexthop_0_m) < 3)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_10()

        def select_action():
            return If(ma_nexthop_0.action(nexthop_0_m) == 1,
                      on_miss_6(),
                      If(ma_nexthop_0.action(nexthop_0_m) == 2,
                          set_egress_details(BitVec("egress_spec_arg", 9)),
                          # this should be an abort of some form
                          0
                         )
                      )
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.nexthop_index(ingress_metadata)
        return If(key_0 == ma_nexthop_0.key_0(nexthop_0_m),
                  select_action(), default())

    def port_mapping_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_port_mapping_0.action(port_mapping_0_m),
              ma_port_mapping_0.action(port_mapping_0_m) < 2)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_11()

        def select_action():
            return If(ma_port_mapping_0.action(port_mapping_0_m) == 1,
                      set_bd(BitVec("bd_arg", 16)), 0)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_port
        return If(key_0 == ma_port_mapping_0.key_0(port_mapping_0_m),
                  select_action(), default())

    port_mapping_0()
    bd_0()
    ipv4_fib_0()
    ipv4_fib_lpm_0()
    nexthop_0()
    # begin apply
    # skip valid for now
    # this is intended to express the switch case statement
    # If(ipv4_fib_0() == 7, ipv4_fib_lpm_0(), 0)
    # If(ipv4_valid, p4_apply(), Var(False, BoolSort()))
    return output.mk_output(ethernet_ret, ipv4_ret, ingress_metadata_ret, egress_spec)


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    set_option(verbose=10)
    bounds = [ethernet, ipv4, ingress_metadata, bd_0_m, ipv4_fib_0_m,
              ipv4_fib_lpm_0_m, nexthop_0_m, port_mapping_0_m]
    # the equivalence equation
    tv_equiv = ForAll(bounds, (
        control_ingress_0() == control_ingress_1()))

    s.add(tv_equiv)

    print (s.sexpr())
    ret = s.check()
    if ret == sat:
        print (ret)
        print (s.model())
    else:
        print (ret)


if __name__ == '__main__':
    z3_check()
