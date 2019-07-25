from z3 import *
import os

''' SOLVER '''
s = Solver()

''' HEADERS '''
# The input headers of the control pipeline


hdr = Datatype("hdr")
hdr.declare("mk_hdr", ('a', BitVecSort(16)),
            ('b', BitVecSort(16)), ('c', BitVecSort(8)))
hdr = hdr.create()


class HDR():
    name = "hdr"

    def __init__(self):
        self.name = "hdr%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", hdr)
        self.revisions = [self.const]
        self.a = self.a_z3()
        self.b = self.b_z3()
        self.c = self.c_z3()
        self.valid = Const('hdr_valid', BoolSort())

    def a_z3(self):
        return hdr.a(self.const)

    def b_z3(self):
        return hdr.b(self.const)

    def c_z3(self):
        return hdr.c(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", hdr)
        self.revisions.append(self.const)

    def make(self):
        return hdr.mk_hdr(self.a, self.b, self.c)

    def set(self, lvalue, rvalue):
        z3_copy = self.make()
        update = substitute(z3_copy, (lvalue, rvalue))
        self.update()
        return update

    def isValid(self):
        return self.valid

    def setValid(self):
        self.valid == Var(True, BoolSort())


headers = Datatype("headers")
headers.declare(f"mk_headers", ('h', hdr))
headers = headers.create()


class HEADERS():

    def __init__(self):
        self.name = "headers%s" % str(id(self))[-4:]
        self.h = HDR()
        self.const = Const(f"{self.name}_0", headers)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", headers)
        self.revisions.append(self.const)

    def make(self):
        return headers.mk_headers(self.h.make())

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


meta = Datatype("meta")
meta.declare(f"mk_meta", ('x', BitVecSort(8)), ('y', BitVecSort(8)))
meta = meta.create()


class META():

    def __init__(self):
        self.name = "meta%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", meta)
        self.revisions = [self.const]
        self.x = self.x_z3()
        self.y = self.y_z3()

    def x_z3(self):
        return meta.x(self.const)

    def y_z3(self):
        return meta.y(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", meta)
        self.revisions.append(self.const)

    def make(self):
        return meta.mk_meta(self.x, self.y)

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


''' TABLES '''
''' The table constant we are matching with.
 Right now, we have a hacky version of integer values which mimic an enum.
 Each integer value corresponds to a specific action PER table. The number of
 available integer values is constrained. '''
ma_t_0 = Datatype('ma_t_0')
ma_t_0.declare('mk_ma_t_0', ('action', IntSort()))
ma_t_0 = ma_t_0.create()


standard_metadata_t = Datatype("standard_metadata_t")
standard_metadata_t.declare(f"mk_standard_metadata_t",
                            ('ingress_port', BitVecSort(9)),
                            ('egress_spec', BitVecSort(9)),
                            ('egress_port', BitVecSort(9)),
                            ('clone_spec', BitVecSort(32)),
                            ('instance_type', BitVecSort(32)),
                            ('drop', BitVecSort(1)),
                            ('recirculate_port', BitVecSort(16)),
                            ('packet_length', BitVecSort(32)),
                            ('enq_timestamp', BitVecSort(32)),
                            ('enq_qdepth', BitVecSort(19)),
                            ('deq_timedelta', BitVecSort(32)),
                            ('deq_qdepth', BitVecSort(19)),
                            ('ingress_global_timestamp', BitVecSort(48)),
                            ('egress_global_timestamp', BitVecSort(48)),
                            ('lf_field_list', BitVecSort(32)),
                            ('mcast_grp', BitVecSort(16)),
                            ('resubmit_flag', BitVecSort(32)),
                            ('egress_rid', BitVecSort(16)),
                            ('recirculate_flag', BitVecSort(32)),
                            ('checksum_error', BitVecSort(1)),
                            ('priority', BitVecSort(3)),
                            )
standard_metadata_t = standard_metadata_t.create()


''' TABLES '''
''' Standard metadata definitions. These are typically defined by the model
    imported on top of the file.'''


class STANDARD_METADATA_T():

    def __init__(self):
        self.name = "standard_metadata_t%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", standard_metadata_t)
        self.revisions = [self.const]
        self.ingress_port = self.ingress_port_z3()
        self.egress_spec = self.egress_spec_z3()
        self.egress_port = self.egress_port_z3()
        self.clone_spec = self.clone_spec_z3()
        self.instance_type = self.instance_type_z3()
        self.drop = self.drop_z3()
        self.recirculate_port = self.recirculate_port_z3()
        self.packet_length = self.packet_length_z3()
        self.enq_timestamp = self.enq_timestamp_z3()
        self.enq_qdepth = self.enq_qdepth_z3()
        self.deq_timedelta = self.deq_timedelta_z3()
        self.deq_qdepth = self.deq_qdepth_z3()
        self.ingress_global_timestamp = self.ingress_global_timestamp_z3()
        self.egress_global_timestamp = self.egress_global_timestamp_z3()
        self.lf_field_list = self.lf_field_list_z3()
        self.mcast_grp = self.mcast_grp_z3()
        self.resubmit_flag = self.resubmit_flag_z3()
        self.egress_rid = self.egress_rid_z3()
        self.recirculate_flag = self.recirculate_flag_z3()
        self.checksum_error = self.checksum_error_z3()
        self.priority = self.priority_z3()

    def ingress_port_z3(self):
        return standard_metadata_t.ingress_port(self.const)

    def egress_spec_z3(self):
        return standard_metadata_t.egress_spec(self.const)

    def egress_port_z3(self):
        return standard_metadata_t.egress_port(self.const)

    def clone_spec_z3(self):
        return standard_metadata_t.clone_spec(self.const)

    def instance_type_z3(self):
        return standard_metadata_t.instance_type(self.const)

    def drop_z3(self):
        return standard_metadata_t.drop(self.const)

    def recirculate_port_z3(self):
        return standard_metadata_t.recirculate_port(self.const)

    def packet_length_z3(self):
        return standard_metadata_t.packet_length(self.const)

    def enq_timestamp_z3(self):
        return standard_metadata_t.enq_timestamp(self.const)

    def enq_qdepth_z3(self):
        return standard_metadata_t.enq_qdepth(self.const)

    def deq_timedelta_z3(self):
        return standard_metadata_t.deq_timedelta(self.const)

    def deq_qdepth_z3(self):
        return standard_metadata_t.deq_qdepth(self.const)

    def ingress_global_timestamp_z3(self):
        return standard_metadata_t.ingress_global_timestamp(self.const)

    def egress_global_timestamp_z3(self):
        return standard_metadata_t.egress_global_timestamp(self.const)

    def lf_field_list_z3(self):
        return standard_metadata_t.lf_field_list(self.const)

    def mcast_grp_z3(self):
        return standard_metadata_t.mcast_grp(self.const)

    def resubmit_flag_z3(self):
        return standard_metadata_t.resubmit_flag(self.const)

    def egress_rid_z3(self):
        return standard_metadata_t.egress_rid(self.const)

    def recirculate_flag_z3(self):
        return standard_metadata_t.recirculate_flag(self.const)

    def checksum_error_z3(self):
        return standard_metadata_t.checksum_error(self.const)

    def priority_z3(self):
        return standard_metadata_t.priority(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", standard_metadata_t)
        self.revisions.append(self.const)

    def make(self):
        return standard_metadata_t.mk_standard_metadata_t(
            self.ingress_port,
            self.egress_spec,
            self.egress_port,
            self.clone_spec,
            self.instance_type,
            self.drop,
            self.recirculate_port,
            self.packet_length,
            self.enq_timestamp,
            self.enq_qdepth,
            self.deq_timedelta,
            self.deq_qdepth,
            self.ingress_global_timestamp,
            self.egress_global_timestamp,
            self.lf_field_list,
            self.mcast_grp,
            self.resubmit_flag,
            self.egress_rid,
            self.recirculate_flag,
            self.checksum_error,
            self.priority,
        )

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


''' INPUT VARIABLES AND MATCH-ACTION ENTRIES'''

''' Initialize the header and match-action constraints
 These are our inputs and outputs
 Think of it as the header inputs after they have been parsed'''

''' OUTPUT '''
''' The final output of the control pipeline in a single data type.
 This corresponds to the arguments of the control function'''
inouts = Datatype("inouts")
inouts.declare(f"mk_inouts", ('h', headers), ('m', meta),
               ('sm', standard_metadata_t))
inouts = inouts.create()


class INOUTS():
    name = "inouts"

    def __init__(self):
        self.name = "inouts%s" % str(id(self))[-4:]
        self.h = HEADERS()
        self.m = META()
        self.sm = STANDARD_METADATA_T()
        self.const = Const(f"{self.name}_0", inouts)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", inouts)
        self.revisions.append(self.const)

    def make(self):
        return inouts.mk_inouts(self.h.make(), self.m.make(), self.sm.make())

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


''' INPUT CONTROL '''
# The possible table entries
t_0_m = Const('t_0_m', ma_t_0)
# Reduce the range of action outputs to the total number of actions
# In this case we only have 2 actions
s.add(0 < ma_t_0.action(t_0_m), ma_t_0.action(t_0_m) < 9)


def step(func_chain, inouts, assigns):
    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        inouts = copy.deepcopy(inouts)  # emulate pass-by-value behavior
        assigns.append(next_fun(func_chain, inouts))
    else:
        assigns.append(True)
    return And(assigns)


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same

    inouts = INOUTS()
    bounds = [inouts.const, t_0_m]
    # the equivalence equation
    tv_equiv = simplify(control_ingress_0(inouts) != control_ingress_1(inouts))
    s.add(Exists(bounds, tv_equiv))
    # tv_equiv = simplify(control_ingress_1()) != simplify(control_ingress_2())
    # s.add(Exists(bounds, tv_equiv))
    # tv_equiv = simplify(control_ingress_2()) != simplify(control_ingress_3())
    # s.add(Exists(bounds, tv_equiv))
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


def control_ingress_0(inouts):
    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def case0(func_chain, inouts):
        ''' This is an action '''
        assigns = []
        rval = Int2BV(Concat(Extract(15, 0, Concat(
            BitVecVal(0, 16), inouts.h.h.a)), BitVecVal(0, 16)), 8)
        inouts.h.h.c = rval
        inouts.set(inouts.h.h.c, rval)
        return step(func_chain, inouts, assigns)

    # @name("ingress.c.t") table t_0 {
    def t_0(func_chain, inouts):
        ''' This is a table '''

        # actions = {
        #     c_a_0();
        #     NoAction_0();
        # }
        def actions():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This is an exclusive operation, so only Xoring is valid.
            '''
            actions = []
            actions.append(Implies(ma_t_0.action(t_0_m) == 1,
                                   case0(func_chain, inouts)))
            actions.append(False)
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        # key = {
        #     h.h.a + h.h.a: exact @name("e") ;
        # }
        key_matches = []
        # It is an exact match, so we use direct comparison
        key_matches.append(False)

        # default_action = NoAction_0();
        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return case0(func_chain, inouts)

        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), actions(), default())

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []
        # t_0.apply();
        func_chain.append(t_0)
        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], inouts=inouts)


def control_ingress_1(inouts):
    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def case0(func_chain, inouts):
        ''' This is an action '''
        assigns = []
        rval = Int2BV(
            Concat(Extract(15, 0, inouts.h.h.a), BitVecVal(0, 16)), 8)
        inouts.h.h.c = rval
        inouts.set(inouts.h.h.c, rval)
        return step(func_chain, inouts, assigns)

    # @name("ingress.c.t") table t_0 {
    def t_0(func_chain, inouts):
        ''' This is a table '''

        # actions = {
        #     c_a_0();
        #     NoAction_0();
        # }
        def actions():
            ''' This is a special macro to define action selection. We treat
            selection as a chain of implications. If we match, then the clause
            returned by the action must be valid.
            This is an exclusive operation, so only Xoring is valid.
            '''
            actions = []
            actions.append(Implies(ma_t_0.action(t_0_m) == 1,
                                   case0(func_chain, inouts)))
            actions.append(False)
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        # key = {
        #     h.h.a + h.h.a: exact @name("e") ;
        # }
        key_matches = []
        # It is an exact match, so we use direct comparison
        key_matches.append(False)

        # default_action = NoAction_0();
        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return case0(func_chain, inouts)

        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), actions(), default())

    def apply():
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        func_chain = []
        # t_0.apply();
        func_chain.append(t_0)
        return func_chain
    # return the apply function as sequence of logic clauses
    func_chain = apply()
    return step(func_chain, assigns=[], inouts=inouts)


if __name__ == '__main__':
    z3_check()
