from z3 import *


''' SOLVER '''
s = Solver()

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
# reduce the range of action outputs to the total number of actions
s.add(0 < ma_bd_0.action(bd_0_m), ma_bd_0.action(bd_0_m) < 2)

ipv4_fib_0_m = Const('ipv4_fib_0_m', ma_ipv4_fib_0)
# reduce the range of action outputs to the total number of actions
s.add(0 < ma_ipv4_fib_0.action(ipv4_fib_0_m),
      ma_ipv4_fib_0.action(ipv4_fib_0_m) < 3)

ipv4_fib_lpm_0_m = Const('ipv4_fib_lpm_0_m', ma_ipv4_fib_lpm_0)
# reduce the range of action outputs to the total number of actions
s.add(0 < ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m),
      ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) < 3)

nexthop_0_m = Const('nexthop_0_m', ma_nexthop_0)
# reduce the range of action outputs to the total number of actions
s.add(0 < ma_nexthop_0.action(nexthop_0_m),
      ma_nexthop_0.action(nexthop_0_m) < 3)

port_mapping_0_m = Const('port_mapping_0_m', ma_port_mapping_0)
# reduce the range of action outputs to the total number of actions
s.add(0 < ma_port_mapping_0.action(port_mapping_0_m),
      ma_port_mapping_0.action(port_mapping_0_m) < 2)


# non-modifiable input variable
ingress_port = BitVec("ingress_port", 16)


def step(func_list, rets, assignments):
    rets = list(rets)  # do not propagate the list per step
    if func_list:
        next_fun = func_list[0]
        func_list = func_list[1:]
        assignments.append(next_fun(func_list, rets))
    else:
        assignments.append(True)
    return And(assignments)


def control_ingress_0():

    # The output header, one variable per modification
    ret_0 = Const("ret_0", p4_output)

    def NoAction_1(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def NoAction_8(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def NoAction_9(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def NoAction_10(func_list, rets):
        ''' This is an action '''
        assignments = []
        assignments.append(True)
        return step(func_list, rets, assignments)

    def NoAction_11(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def set_vrf(func_list, rets, vrf_arg):
        assignments = []

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            ingress_metadata_t.mk_ingress_metadata_t(
                vrf_arg,
                ingress_metadata_t.bd(p4_output.ingress_metadata_t(ret_0)),
                ingress_metadata_t.nexthop_index(
                    p4_output.ingress_metadata_t(ret_0))),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)

        return step(func_list, rets, assignments)

    def on_miss_2(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def on_miss_5(func_list, rets):
        ''' This is an action '''
        # NoAction just returns the current header as is
        assignments = []
        return step(func_list, rets, assignments)

    def on_miss_6(func_list, rets):
        ''' This is an action '''
        # NoAction just returns the current header as is
        # This action creates a new header type where b is set to a
        assignments = []
        return step(func_list, rets, assignments)

    def fib_hit_nexthop(func_list, rets, nexthop_index_arg):
        assignments = []

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            ingress_metadata_t.mk_ingress_metadata_t(
                ingress_metadata_t.vrf(p4_output.ingress_metadata_t(ret_0)),
                ingress_metadata_t.bd(p4_output.ingress_metadata_t(ret_0)),
                nexthop_index_arg),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            ipv4_t.mk_ipv4_t(
                ipv4_t.version(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.ihl(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.diffserv(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.totalLen(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.identification(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.flags(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.fragOffset(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.ttl(p4_output.ipv4_t(
                    rets[prev_ret])) + BitVecVal(255, 8),
                ipv4_t.protocol(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.hdrChecksum(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.srcAddr(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.dstAddr(p4_output.ipv4_t(rets[prev_ret])),
            ),
            p4_output.ingress_metadata_t(rets[prev_ret]),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)
        return step(func_list, rets, assignments)

    def fib_hit_nexthop_2(func_list, rets, nexthop_index_arg):
        assignments = []

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            ingress_metadata_t.mk_ingress_metadata_t(
                ingress_metadata_t.vrf(p4_output.ingress_metadata_t(ret_0)),
                ingress_metadata_t.bd(p4_output.ingress_metadata_t(ret_0)),
                nexthop_index_arg),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            ipv4_t.mk_ipv4_t(
                ipv4_t.version(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.ihl(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.diffserv(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.totalLen(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.identification(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.flags(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.fragOffset(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.ttl(p4_output.ipv4_t(
                    rets[prev_ret])) + BitVecVal(255, 8),
                ipv4_t.protocol(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.hdrChecksum(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.srcAddr(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.dstAddr(p4_output.ipv4_t(rets[prev_ret])),
            ),
            p4_output.ingress_metadata_t(rets[prev_ret]),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)
        return step(func_list, rets, assignments)

    def set_egress_details(func_list, rets, egress_spec_arg):
        assignments = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            p4_output.ingress_metadata_t(rets[prev_ret]),
            egress_spec_arg)
        assignments.append(rets[new_ret] == assign)
        return step(func_list, rets, assignments)

    def set_bd(func_list, rets, bd_arg):
        assignments = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            ingress_metadata_t.mk_ingress_metadata_t(
                ingress_metadata_t.vrf(p4_output.ingress_metadata_t(ret_0)),
                bd_arg,
                ingress_metadata_t.nexthop_index(
                    p4_output.ingress_metadata_t(ret_0))),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)

        return step(func_list, rets, assignments)

    def bd_0(func_list, rets):

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_1(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(ma_bd_0.action(bd_0_m) == 1,
                                   set_vrf(func_list, rets, BitVec("vrf_arg", 12))))
            actions.append(False)
            return Xor(*actions)
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.bd(ingress_metadata)
        return If(key_0 == ma_bd_0.key_0(bd_0_m),
                  select_action(), default())

    def ipv4_fib_0(func_list, rets):

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_8(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1,
                                   on_miss_2(func_list, rets)))
            actions.append(Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 2,
                                   fib_hit_nexthop(func_list,
                                                   rets, BitVec("nexthop_index_arg", 16))))
            return Xor(*actions)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.vrf(ingress_metadata)
        key_1 = ipv4_t.dstAddr(ipv4)
        return If(And(key_0 == ma_ipv4_fib_0.key_0(ipv4_fib_0_m),
                      key_1 == ma_ipv4_fib_0.key_1(ipv4_fib_0_m)),
                  select_action(), default())

    def ipv4_fib_lpm_0(func_list, rets):
        # This should be a mask for lpm matches
        # TODO: Make it a proper mask and fix
        masks = [(2**i) - 1 for i in range(32)]

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_9(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(
                ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 1,
                on_miss_5(func_list, rets)))
            actions.append(Implies(
                ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 2,
                fib_hit_nexthop_2(func_list, rets, BitVec("nexthop_index_arg",
                                                          16))))
            return Xor(*actions)
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.vrf(ingress_metadata)
        key_1 = ipv4_t.dstAddr(ipv4)
        return If(And(key_0 == ma_ipv4_fib_lpm_0.key_0(ipv4_fib_lpm_0_m),
                      Or([key_1 & m ==
                          ma_ipv4_fib_lpm_0.key_1(ipv4_fib_lpm_0_m) & m
                          for m in masks])),
                  select_action(), default())

    def nexthop_0(func_list, rets):

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_10(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(ma_nexthop_0.action(nexthop_0_m) == 1,
                                   on_miss_6(func_list, rets)))
            actions.append(Implies(ma_nexthop_0.action(nexthop_0_m) == 2,
                                   set_egress_details(func_list, rets,
                                                      BitVec("egress_spec_arg",
                                                             9))))
            return Xor(*actions)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.nexthop_index(ingress_metadata)
        return If(key_0 == ma_nexthop_0.key_0(nexthop_0_m),
                  select_action(), default())

    def port_mapping_0(func_list, rets):

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_11(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(ma_port_mapping_0.action(
                port_mapping_0_m) == 1, set_bd(func_list, rets,
                                               BitVec("bd_arg", 16))))
            actions.append(False)
            return Xor(*actions)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_port
        return If(key_0 == ma_port_mapping_0.key_0(port_mapping_0_m),
                  select_action(), default())

    def apply():
        # This is the initial version of the program
        func_list = []

        def is_valid_block(func_list, rets):
            sub_list = []
            assignments = []
            sub_list.append(port_mapping_0)
            sub_list.append(bd_0)
            sub_list.append(ipv4_fib_0)

            def switch_block(func_list, rets):
                cases = []
                cases.append(
                    Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1,
                            ipv4_fib_lpm_0(func_list, rets)))
                cases.append(False)
                return Xor(*cases)
            sub_list.append(switch_block)
            sub_list.append(nexthop_0)
            return Implies(ipv4_valid, step(sub_list, rets, assignments))
        func_list.append(is_valid_block)

        return func_list

    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assignments=[], rets=[ret_0])


def control_ingress_1():

    # The output header, one variable per modification
    ret_0 = Const("ret_0", p4_output)

    def NoAction_1(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def NoAction_8(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def NoAction_9(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def NoAction_10(func_list, rets):
        ''' This is an action '''
        assignments = []
        assignments.append(True)
        return step(func_list, rets, assignments)

    def NoAction_11(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def set_vrf(func_list, rets, vrf_arg):
        assignments = []

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            ingress_metadata_t.mk_ingress_metadata_t(
                vrf_arg,
                ingress_metadata_t.bd(p4_output.ingress_metadata_t(ret_0)),
                ingress_metadata_t.nexthop_index(
                    p4_output.ingress_metadata_t(ret_0))),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)

        return step(func_list, rets, assignments)

    def on_miss_2(func_list, rets):
        ''' This is an action '''
        assignments = []
        return step(func_list, rets, assignments)

    def on_miss_5(func_list, rets):
        ''' This is an action '''
        # NoAction just returns the current header as is
        assignments = []
        return step(func_list, rets, assignments)

    def on_miss_6(func_list, rets):
        ''' This is an action '''
        # NoAction just returns the current header as is
        # This action creates a new header type where b is set to a
        assignments = []
        return step(func_list, rets, assignments)

    def fib_hit_nexthop(func_list, rets, nexthop_index_arg):
        assignments = []

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            ingress_metadata_t.mk_ingress_metadata_t(
                ingress_metadata_t.vrf(p4_output.ingress_metadata_t(ret_0)),
                ingress_metadata_t.bd(p4_output.ingress_metadata_t(ret_0)),
                nexthop_index_arg),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            ipv4_t.mk_ipv4_t(
                ipv4_t.version(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.ihl(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.diffserv(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.totalLen(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.identification(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.flags(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.fragOffset(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.ttl(p4_output.ipv4_t(
                    rets[prev_ret])) + BitVecVal(255, 8),
                ipv4_t.protocol(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.hdrChecksum(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.srcAddr(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.dstAddr(p4_output.ipv4_t(rets[prev_ret])),
            ),
            p4_output.ingress_metadata_t(rets[prev_ret]),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)
        return step(func_list, rets, assignments)

    def fib_hit_nexthop_2(func_list, rets, nexthop_index_arg):
        assignments = []

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            ingress_metadata_t.mk_ingress_metadata_t(
                ingress_metadata_t.vrf(p4_output.ingress_metadata_t(ret_0)),
                ingress_metadata_t.bd(p4_output.ingress_metadata_t(ret_0)),
                nexthop_index_arg),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)

        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            ipv4_t.mk_ipv4_t(
                ipv4_t.version(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.ihl(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.diffserv(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.totalLen(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.identification(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.flags(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.fragOffset(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.ttl(p4_output.ipv4_t(
                    rets[prev_ret])) + BitVecVal(255, 8),
                ipv4_t.protocol(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.hdrChecksum(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.srcAddr(p4_output.ipv4_t(rets[prev_ret])),
                ipv4_t.dstAddr(p4_output.ipv4_t(rets[prev_ret])),
            ),
            p4_output.ingress_metadata_t(rets[prev_ret]),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)
        return step(func_list, rets, assignments)

    def set_egress_details(func_list, rets, egress_spec_arg):
        assignments = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            p4_output.ingress_metadata_t(rets[prev_ret]),
            egress_spec_arg)
        assignments.append(rets[new_ret] == assign)
        return step(func_list, rets, assignments)

    def set_bd(func_list, rets, bd_arg):
        assignments = []
        new_ret = len(rets)
        prev_ret = new_ret - 1
        rets.append(Const("ret_%d" % new_ret, p4_output))
        assign = p4_output.mk_output(
            p4_output.ethernet_t(rets[prev_ret]),
            p4_output.ipv4_t(rets[prev_ret]),
            ingress_metadata_t.mk_ingress_metadata_t(
                ingress_metadata_t.vrf(p4_output.ingress_metadata_t(ret_0)),
                bd_arg,
                ingress_metadata_t.nexthop_index(
                    p4_output.ingress_metadata_t(ret_0))),
            p4_output.egress_spec(rets[prev_ret]))
        assignments.append(rets[new_ret] == assign)

        return step(func_list, rets, assignments)

    def bd_0(func_list, rets):

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_1(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(ma_bd_0.action(bd_0_m) == 1,
                                   set_vrf(func_list, rets, BitVec("vrf_arg", 12))))
            actions.append(False)
            return Xor(*actions)
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.bd(ingress_metadata)
        return If(key_0 == ma_bd_0.key_0(bd_0_m),
                  select_action(), default())

    def ipv4_fib_0(func_list, rets):

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_8(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1,
                                   on_miss_2(func_list, rets)))
            actions.append(Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 2,
                                   fib_hit_nexthop(func_list,
                                                   rets, BitVec("nexthop_index_arg", 16))))
            return Xor(*actions)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.vrf(ingress_metadata)
        key_1 = ipv4_t.dstAddr(ipv4)
        return If(And(key_0 == ma_ipv4_fib_0.key_0(ipv4_fib_0_m),
                      key_1 == ma_ipv4_fib_0.key_1(ipv4_fib_0_m)),
                  select_action(), default())

    def ipv4_fib_lpm_0(func_list, rets):
        # This should be a mask for lpm matches
        # TODO: Make it a proper mask and fix
        masks = [(2**i) - 1 for i in range(32)]

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_9(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(
                ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 1,
                on_miss_5(func_list, rets)))
            actions.append(Implies(
                ma_ipv4_fib_lpm_0.action(ipv4_fib_lpm_0_m) == 2,
                fib_hit_nexthop_2(func_list, rets, BitVec("nexthop_index_arg",
                                                          16))))
            return Xor(*actions)
        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.vrf(ingress_metadata)
        key_1 = ipv4_t.dstAddr(ipv4)
        return If(And(key_0 == ma_ipv4_fib_lpm_0.key_0(ipv4_fib_lpm_0_m),
                      Or([key_1 & m ==
                          ma_ipv4_fib_lpm_0.key_1(ipv4_fib_lpm_0_m) & m
                          for m in masks])),
                  select_action(), default())

    def nexthop_0(func_list, rets):

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_10(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(ma_nexthop_0.action(nexthop_0_m) == 1,
                                   on_miss_6(func_list, rets)))
            actions.append(Implies(ma_nexthop_0.action(nexthop_0_m) == 2,
                                   set_egress_details(func_list, rets,
                                                      BitVec("egress_spec_arg",
                                                             9))))
            return Xor(*actions)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_metadata_t.nexthop_index(ingress_metadata)
        return If(key_0 == ma_nexthop_0.key_0(nexthop_0_m),
                  select_action(), default())

    def port_mapping_0(func_list, rets):

        def default():
            # The default action
            # It is set to NoAction in this case
            return NoAction_11(func_list, rets)

        def select_action():
            actions = []
            actions.append(Implies(ma_port_mapping_0.action(
                port_mapping_0_m) == 1, set_bd(func_list, rets,
                                               BitVec("bd_arg", 16))))
            actions.append(False)
            return Xor(*actions)

        # This is a table match where we look up the provided key
        # Key probably has to be a datatype, too
        key_0 = ingress_port
        return If(key_0 == ma_port_mapping_0.key_0(port_mapping_0_m),
                  select_action(), default())

    def apply():
        # This is the initial version of the program
        func_list = []

        def is_valid_block(func_list, rets):
            sub_list = []
            assignments = []
            sub_list.append(port_mapping_0)
            sub_list.append(bd_0)
            sub_list.append(ipv4_fib_0)

            def switch_block(func_list, rets):
                cases = []
                cases.append(
                    Implies(ma_ipv4_fib_0.action(ipv4_fib_0_m) == 1,
                            ipv4_fib_lpm_0(func_list, rets)))
                cases.append(False)
                return Xor(*cases)
            sub_list.append(switch_block)
            sub_list.append(nexthop_0)
            return Implies(ipv4_valid, step(sub_list, rets, assignments))
        func_list.append(is_valid_block)

        return func_list

    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assignments=[], rets=[ret_0])


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    set_option(verbose=10)
    bounds = [ethernet, ipv4, ingress_metadata, bd_0_m, ipv4_fib_0_m,
              ipv4_fib_lpm_0_m, nexthop_0_m, port_mapping_0_m]
    # the equivalence equation
    tv_equiv = simplify(control_ingress_0()) != simplify(control_ingress_1())
    s.add(tv_equiv)

    print(tv_equiv)
    # print (s.sexpr())
    ret = s.check()
    if ret == sat:
        print(ret)
        print(s.model())
    else:
        print(ret)


if __name__ == '__main__':
    z3_check()
