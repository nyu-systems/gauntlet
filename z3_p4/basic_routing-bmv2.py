from z3 import *

''' HEADERS '''
# The input headers of the control pipeline
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

''' TABLES '''
''' The table constant we are matching with.
 Actually this should be a match action tuple that picks the next action
 How to implement that? Some form of array?
 Right now, we have a hacky version of integer values which mimic an enum.
 Each integer value corresponds to a specific action PER table. The number of
 available integer values is constrained. '''
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


''' OUTPUT '''

# the final output of the control pipeline in a single datatype
p4_output = Datatype('p4_output')
p4_output.declare('mk_output',
                  ('ethernet_t', ethernet_t), ('ipv4_t', ipv4_t),
                  ('ingress_metadata_t', ingress_metadata_t),
                  ('egress_spec', BitVecSort(9)))
p4_output = p4_output.create()


''' INPUT VARIABLES AND MATCH-ACTION ENTRIES'''

# Initialize the header and match-action constraints
# These are our inputs
# Think of it as the header inputs after they have been parsed
ethernet = Const('ethernet', ethernet_t)
ethernet_valid = Const('ethernet_valid', BoolSort())
ipv4 = Const('ipv4', ipv4_t)
ipv4_valid = Const('ipv4_valid', BoolSort())
ingress_metadata = Const('ingress_metadata', ingress_metadata_t)

# The possible table entries
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

    constraints = []
    ret = Const('ret', p4_output)

    def NoAction_1():
        return Var(True, BoolSort())

    def NoAction_8():
        return Var(True, BoolSort())

    def NoAction_9():
        return Var(True, BoolSort())

    def NoAction_10():
        return Var(True, BoolSort())

    def NoAction_11():
        return Var(True, BoolSort())

    def set_vrf(vrf_arg):
        updates = []
        updates.append(ingress_metadata_t.vrf(
            p4_output.ingress_metadata_t(ret)) == vrf_arg)
        return And(updates)

    def on_miss_2():
        return Var(True, BoolSort())

    def on_miss_5():
        return Var(True, BoolSort())

    def on_miss_6():
        return Var(True, BoolSort())

    def fib_hit_nexthop(nexthop_index_arg):
        updates = []
        updates.append(ingress_metadata_t.nexthop_index(
            p4_output.ingress_metadata_t(ret)) == nexthop_index_arg)
        ttl = ipv4_t.ttl(p4_output.ipv4_t(ret))
        new_ttl = ipv4_t.ttl(ipv4) + BitVecVal(255, 8)
        updates.append(ttl == new_ttl)
        return And(updates)

    def fib_hit_nexthop_2(nexthop_index_arg):
        updates = []
        updates.append(ingress_metadata_t.nexthop_index(
            p4_output.ingress_metadata_t(ret)) == nexthop_index_arg)
        ttl = ipv4_t.ttl(p4_output.ipv4_t(ret))
        new_ttl = ipv4_t.ttl(ipv4) + BitVecVal(255, 8)
        updates.append(ttl == new_ttl)
        return And(updates)

    def set_egress_details(egress_spec_arg):
        updates = []
        updates.append(p4_output.egress_spec(ret) == egress_spec_arg)
        return And(updates)

    def set_bd(bd_arg):
        updates = []
        updates.append(ingress_metadata_t.bd(
            p4_output.ingress_metadata_t(ret)) == bd_arg)
        return And(updates)

    def bd_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_bd_0.action(bd_0_m), ma_bd_0.action(bd_0_m) < 2)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_1()

        def select_action():
            actions = []
            actions.append(Implies(ma_bd_0.action(bd_0_m) == 1,
                                   set_vrf(BitVec("vrf_arg", 12))))
            return And(actions)
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
            actions = []
            actions.append(Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1,
                                   on_miss_2()))
            actions.append(Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 2,
                                   fib_hit_nexthop(BitVec("nexthop_index_arg",
                                                          16))))
            return And(actions)

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
            actions = []
            actions.append(Implies(
                ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 1,
                on_miss_5()))
            actions.append(Implies(
                ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 2,
                fib_hit_nexthop_2(BitVec("nexthop_index_arg",
                                         16))))
            return And(actions)
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
            actions = []
            actions.append(Implies(ma_nexthop_0.action(nexthop_0_m) == 1,
                                   on_miss_6()))
            actions.append(Implies(ma_nexthop_0.action(nexthop_0_m) == 2,
                                   set_egress_details(BitVec("egress_spec_arg",
                                                             9))))
            return And(actions)

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
            actions = []
            actions.append(Implies(ma_port_mapping_0.action(
                port_mapping_0_m) == 1, set_bd(BitVec("bd_arg", 16))))
            return And(actions)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_port
        return If(key_0 == ma_port_mapping_0.key_0(port_mapping_0_m),
                  select_action(), default())

    # begin apply
    # this is a valid case
    ip4_valid_constraints = []
    ip4_valid_constraints.append(port_mapping_0())
    ip4_valid_constraints.append(bd_0())
    ip4_valid_constraints.append(ipv4_fib_0())
    # this is intended to express the switch case statement
    ip4_valid_constraints.append(
        Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1, ipv4_fib_lpm_0()))
    ip4_valid_constraints.append(nexthop_0())
    constraints.append(Implies(ipv4_valid, And(ip4_valid_constraints)))
    return And(constraints)


def control_ingress_1():
    # This is the initial version of the program

    constraints = []
    ret = Const('ret', p4_output)

    def NoAction_1():
        return Var(True, BoolSort())

    def NoAction_8():
        return Var(True, BoolSort())

    def NoAction_9():
        return Var(True, BoolSort())

    def NoAction_10():
        return Var(True, BoolSort())

    def NoAction_11():
        return Var(True, BoolSort())

    def set_vrf(vrf_arg):
        updates = []
        updates.append(ingress_metadata_t.vrf(
            p4_output.ingress_metadata_t(ret)) == vrf_arg)
        return And(updates)

    def on_miss_2():
        return Var(True, BoolSort())

    def on_miss_5():
        return Var(True, BoolSort())

    def on_miss_6():
        return Var(True, BoolSort())

    def fib_hit_nexthop(nexthop_index_arg):
        updates = []
        updates.append(ingress_metadata_t.nexthop_index(
            p4_output.ingress_metadata_t(ret)) == nexthop_index_arg)
        ttl = ipv4_t.ttl(p4_output.ipv4_t(ret))
        new_ttl = ipv4_t.ttl(ipv4) + BitVecVal(255, 8)
        updates.append(ttl == new_ttl)
        return And(updates)

    def fib_hit_nexthop_2(nexthop_index_arg):
        updates = []
        updates.append(ingress_metadata_t.nexthop_index(
            p4_output.ingress_metadata_t(ret)) == nexthop_index_arg)
        ttl = ipv4_t.ttl(p4_output.ipv4_t(ret))
        new_ttl = ipv4_t.ttl(ipv4) + BitVecVal(255, 8)
        updates.append(ttl == new_ttl)
        return And(updates)

    def set_egress_details(egress_spec_arg):
        updates = []
        updates.append(p4_output.egress_spec(ret) == egress_spec_arg)
        return And(updates)

    def set_bd(bd_arg):
        updates = []
        updates.append(ingress_metadata_t.bd(
            p4_output.ingress_metadata_t(ret)) == bd_arg)
        return And(updates)

    def bd_0():
        # reduce the range of action outputs to the total number of actions
        s.add(0 < ma_bd_0.action(bd_0_m), ma_bd_0.action(bd_0_m) < 2)

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_1()

        def select_action():
            actions = []
            actions.append(Implies(ma_bd_0.action(bd_0_m) == 1,
                                   set_vrf(BitVec("vrf_arg", 12))))
            return And(actions)
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
            actions = []
            actions.append(Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1,
                                   on_miss_2()))
            actions.append(Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 2,
                                   fib_hit_nexthop(BitVec("nexthop_index_arg",
                                                          16))))
            return And(actions)

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
            actions = []
            actions.append(Implies(
                ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 1,
                on_miss_5()))
            actions.append(Implies(
                ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 2,
                fib_hit_nexthop_2(BitVec("nexthop_index_arg",
                                         16))))
            return And(actions)
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
            actions = []
            actions.append(Implies(ma_nexthop_0.action(nexthop_0_m) == 1,
                                   on_miss_6()))
            actions.append(Implies(ma_nexthop_0.action(nexthop_0_m) == 2,
                                   set_egress_details(BitVec("egress_spec_arg",
                                                             9))))
            return And(actions)

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
            actions = []
            actions.append(Implies(ma_port_mapping_0.action(
                port_mapping_0_m) == 1, set_bd(BitVec("bd_arg", 16))))
            return And(actions)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_port
        return If(key_0 == ma_port_mapping_0.key_0(port_mapping_0_m),
                  select_action(), default())

    # begin apply
    # this is a valid case
    ip4_valid_constraints = []
    ip4_valid_constraints.append(port_mapping_0())
    ip4_valid_constraints.append(bd_0())
    ip4_valid_constraints.append(ipv4_fib_0())
    # this is intended to express the switch case statement
    ip4_valid_constraints.append(
        Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1, ipv4_fib_lpm_0()))
    ip4_valid_constraints.append(nexthop_0())
    # end of the block, append the condition
    constraints.append(Implies(ipv4_valid, And(ip4_valid_constraints)))
    return And(constraints)


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    set_option(verbose=10)
    bounds = [ethernet, ipv4, ingress_metadata, bd_0_m, ipv4_fib_0_m,
              ipv4_fib_lpm_0_m, nexthop_0_m, port_mapping_0_m]
    # the equivalence equation
    tv_equiv = Exists(bounds, simplify(control_ingress_0()) !=
                      simplify(control_ingress_1()))
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
