from z3 import *
import os

''' Standard metadata definitions. These are typically defined by the model
    imported on top of the file.'''

standard_metadata_t = Datatype("standard_metadata_t")
standard_metadata_t.declare("mk_standard_metadata_t",
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


''' HEADERS '''
# The input headers of the control pipeline

hdr = Datatype("hdr")
hdr.declare("mk_hdr", ('a', BitVecSort(32)),
            ('b', BitVecSort(32)))
hdr = hdr.create()


class HDR():
    name = "hdr"

    def __init__(self):
        self.name = "hdr%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", hdr)
        self.revisions = [self.const]
        self.a = self.a_z3()
        self.b = self.b_z3()
        self.valid = Const('hdr_valid', BoolSort())

    def a_z3(self):
        return hdr.a(self.const)

    def b_z3(self):
        return hdr.b(self.const)

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", hdr)
        self.revisions.append(self.const)

    def make(self):
        return hdr.mk_hdr(self.a, self.b)

    def set(self, lvalue, rvalue):
        z3_copy = self.make()
        update = substitute(z3_copy, (lvalue, rvalue))
        self.update()
        return update

    def isValid(self):
        return self.valid

    def setValid(self):
        self.valid == Var(True, BoolSort())


''' STRUCTS '''
# Data structures that were declared globally

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
meta.declare(f"mk_meta")
meta = meta.create()


class META():

    def __init__(self):
        self.name = "meta%s" % str(id(self))[-4:]
        self.const = Const(f"{self.name}_0", meta)
        self.revisions = [self.const]

    def update(self):
        index = len(self.revisions)
        self.const = Const(f"{self.name}_{index}", meta)
        self.revisions.append(self.const)

    def make(self):
        return meta.mk_meta

    def set(self, lvalue, rvalue):
        copy = self.make()
        update = substitute(copy, (lvalue, rvalue))
        self.update()
        return update


''' INPUT VARIABLES '''

''' Initialize the header  These are our inputs and outputs
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


def step(func_chain, inouts, expr=True):
    ''' The step function ensures that modifications are propagated to
    all subsequent operations. This is important to guarantee correctness with
    branching or local modification. '''
    if func_chain:
        next_fun = func_chain[0]
        func_chain = func_chain[1:]
        # emulate pass-by-value behavior
        inouts = copy.deepcopy(inouts)
        expr = next_fun(func_chain, inouts)
    return expr


def control_ingress_0(s, inouts):
    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_0(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        assigns = []
        expr = And(assigns)
        return step(func_chain, inouts, expr)

    # @name("ingress.c.a") action c_a_0() {
    #     h.h.b = h.h.a;
    # }
    def c_a_0(func_chain, inouts):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        # This updates an existing output variable so  we need a new version
        # The new constant is appended to the existing list of constants
        # Now we create the new version by using a data type constructor
        # The data type constructor uses the values from the previous
        # variable version, except for the update target.
        assigns = []
        inouts.h.h.b = inouts.h.h.a
        update = inouts.set(inouts.h.h.b, inouts.h.h.a)
        assigns.append(inouts.const == update)
        expr = And(assigns)
        return step(func_chain, inouts, expr)

    # @name("ingress.c.t") table c_t {
    def c_t(func_chain, inouts):
        ''' This is a table '''

        ''' The table constant we are matching with.
         Right now, we have a hacky version of integer values which
         mimic an enum. Each integer value corresponds to a specific
         action PER table. The number of available integer values is
         constrained. '''
        ma_c_t = Datatype('ma_c_t')
        ma_c_t.declare('mk_ma_c_t', ('key_0', BitVecSort(32)),
                       ('action', IntSort()))
        ma_c_t = ma_c_t.create()
        # The possible table entries as constant
        c_t_m = Const('c_t_m', ma_c_t)

        # Reduce the range of action outputs to the total number of actions
        # In this case we only have 2 actions
        s.add(0 < ma_c_t.action(c_t_m), ma_c_t.action(c_t_m) < 3)

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
            actions.append(Implies(ma_c_t.action(c_t_m) == 1,
                                   c_a_0(func_chain, inouts)))
            actions.append(Implies(ma_c_t.action(c_t_m) == 2,
                                   NoAction_0(func_chain, inouts)))
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        # key = {
        #     h.h.a + h.h.a: exact @name("e") ;
        # }
        key_matches = []
        c_t_key_0 = inouts.h.h.a + inouts.h.h.a
        # It is an exact match, so we use direct comparison
        key_matches.append(c_t_key_0 == ma_c_t.key_0(c_t_m))

        # default_action = NoAction_0();
        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0(func_chain, inouts)

        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), actions(), default())

    def apply(func_chain, inouts):
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        sub_chain = []
        # c_t.apply();
        sub_chain.append(c_t)

        def output_update(func_chain, inouts):
            rval = BitVecVal(0, 9)
            inouts.sm.egress_spec = rval
            update = inouts.set(inouts.sm.egress_spec, rval)
            expr = (inouts.const == update)
            return step(func_chain, inouts, expr)
        # sm.egress_spec = 9w0
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)
    # return the apply function as sequence of logic clauses
    return step(func_chain=[apply], inouts=inouts)


def control_ingress_1(s, inouts):
    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_0(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        assigns = []
        expr = And(assigns)
        return step(func_chain, inouts, expr)

    # @name("ingress.c.a") action c_a_0() {
    #     h.h.b = h.h.a;
    # }
    def c_a_0(func_chain, inouts):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        # This updates an existing output variable so  we need a new version
        # The new constant is appended to the existing list of constants
        # Now we create the new version by using a data type constructor
        # The data type constructor uses the values from the previous
        # variable version, except for the update target.
        assigns = []
        inouts.h.h.b = inouts.h.h.a
        update = inouts.set(inouts.h.h.b, inouts.h.h.a)
        assigns.append(inouts.const == update)
        expr = And(assigns)
        return step(func_chain, inouts, expr)

    # The key is defined in the control function
    # Practically, this is a placeholder variable
    key_0 = BitVec("key_0", 32)  # bit<32> key_0;

    # @name("ingress.c.t") table c_t {
    def c_t(func_chain, inouts):
        ''' This is a table '''

        ''' The table constant we are matching with.
         Right now, we have a hacky version of integer values which
         mimic an enum. Each integer value corresponds to a specific
         action PER table. The number of available integer values is
         constrained. '''
        ma_c_t = Datatype('ma_c_t')
        ma_c_t.declare('mk_ma_c_t', ('key_0', BitVecSort(32)),
                       ('action', IntSort()))
        ma_c_t = ma_c_t.create()
        # The possible table entries as constant
        c_t_m = Const('c_t_m', ma_c_t)

        # Reduce the range of action outputs to the total number of actions
        # In this case we only have 2 actions
        s.add(0 < ma_c_t.action(c_t_m), ma_c_t.action(c_t_m) < 3)

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
            actions.append(Implies(ma_c_t.action(c_t_m) == 1,
                                   c_a_0(func_chain, inouts)))
            actions.append(Implies(ma_c_t.action(c_t_m) == 2,
                                   NoAction_0(func_chain, inouts)))
            return Xor(*actions)

        # The keys of the table are compared with the input keys.
        # In this case we are matching a single value
        # key = {
        #     h.h.a + h.h.a: exact @name("e") ;
        # }
        key_matches = []
        # We access the global variable key_0, which has been updated before
        c_t_key_0 = key_0
        # It is an exact match, so we use direct comparison
        key_matches.append(c_t_key_0 == ma_c_t.key_0(c_t_m))

        # default_action = NoAction_0();
        def default():
            ''' The default action '''
            # It is set to NoAction in this case
            return NoAction_0(func_chain, inouts)

        # This is a table match where we look up the provided key
        # If we match select the associated action, else use the default action
        return If(And(key_matches), actions(), default())

    def apply(func_chain, inouts):
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        sub_chain = []

        # {
        def block(func_chain, inouts):
            sub_chain = []

            def local_update(func_chain, inouts):
                ''' Updates to local variables will not play a role in the
                final output. We do not need to add new constraints. Instead,
                we update the python variable directly for later use. The
                variable is accessed using the nonlocal keyword. '''
                # key_0 is updated to have the value h.h.a + h.h.a
                nonlocal key_0
                key_0 = inouts.h.h.a + inouts.h.h.a
                return step(func_chain, inouts)
            # key_0 = h.h.a + h.h.a;
            sub_chain.append(local_update)
            # c_t.apply();
            sub_chain.append(c_t)

            sub_chain.extend(func_chain)
            return step(sub_chain, inouts)
        # }
        sub_chain.append(block)

        def output_update(func_chain, inouts):
            rval = BitVecVal(0, 9)
            inouts.sm.egress_spec = rval
            update = inouts.set(inouts.sm.egress_spec, rval)
            expr = (inouts.const == update)
            return step(func_chain, inouts, expr)
        # sm.egress_spec = 9w0
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)
    # return the apply function as sequence of logic clauses
    return step(func_chain=[apply], inouts=inouts)


def z3_check():
    # The equivalence check of the solver
    # For all input packets and possible table matches the programs should
    # be the same
    ''' SOLVER '''
    s = Solver()

    inouts = INOUTS()
    bounds = [inouts.const]
    # the equivalence equation
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
