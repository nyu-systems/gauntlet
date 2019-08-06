from p4z3_base import *

''' Model imports at the top of the p4 file '''
from v1model import *


''' HEADERS '''
# The input headers of the control pipeline
# Datatypes have to be declared outside the type object because of issues with
# deepcopy()

# header hdr {
#     bit<32> a;
#     bit<32> b;
# }
z3_args = [('a', BitVecSort(32)), ('b', BitVecSort(32))]
hdr, HDR = z3_reg.register_z3_type("hdr", Header, z3_args)


''' STRUCTS '''
# Data structures that were declared globally

# struct Headers {
#     hdr h;
# }
z3_args = [('h', hdr)]
headers, HEADERS = z3_reg.register_z3_type("headers", Struct, z3_args)


# struct Meta {
# }
z3_args = []
meta, META = z3_reg.register_z3_type("meta", Struct, z3_args)


''' OUTPUT '''
''' Initialize the header  These are our inputs and outputs
 Think of it as the header inputs after they have been parsed.
 The final output of the control pipeline in a single data type.
 This corresponds to the arguments of the control function'''

# control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm)
z3_args = [('h', headers), ('m', meta), ('sm', standard_metadata_t)]
inouts, INOUTS = z3_reg.register_z3_type("inouts", Struct, z3_args)


def control_ingress_0(s, inouts):
    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_0(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

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
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = inouts.h.h.a
            expr = inouts.set("h.h.b", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)
    # @name("ingress.c.t") table c_t {

    # @name("ingress.c.t") table c_t {
    class c_t(Table):
        ''' This is a table '''
        ''' The table constant we are matching with.
         Right now, we have a hacky version of integer values which
         mimic an enum. Each integer value corresponds to a specific
         action PER table. The number of available integer values is
         constrained. '''
        ma_c_t = Datatype('ma_c_t')
        ma_c_t.declare('mk_ma_c_t', ('key_0', BitVecSort(32)),
                       ('action', IntSort()))
        ma = ma_c_t.create()

        @classmethod
        def table_match(cls, inouts):
            # The keys of the table are compared with the input keys.
            # In this case we are matching a single value
            # key = {
            #     h.h.a + h.h.a: exact @name("e") ;
            # }
            key_matches = []
            # The key is an addition of two variables
            c_t_key_0 = inouts.h.h.a + inouts.h.h.a
            # It is an exact match, so we use direct comparison
            key_matches.append(c_t_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

        # The possible table entries as constant
        m = Const('c_t_m', ma)
        # actions = {
        #     c_a_0();
        #     NoAction_0();
        # }
        actions = {
            "c_a_0": (1, (c_a_0, ())),
            "NoAction_0": (2, (NoAction_0, ())),
        }
        actions["default"] = (0, (NoAction_0, ()))

    def apply(func_chain, inouts):
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        sub_chain = []
        # c_t.apply();
        sub_chain.append(c_t.apply)

        def output_update(func_chain, inouts):
            rval = BitVecVal(0, 9)
            update = inouts.set("sm.egress_spec", rval)
            expr = (update)
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
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

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
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = inouts.h.h.a
            expr = inouts.set("h.h.b", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    # The key is defined in the control function
    # Practically, this is a placeholder variable
    key_0 = BitVec("key_0", 32)  # bit<32> key_0;

    # @name("ingress.c.t") table c_t {
    class c_t(Table):
        ''' This is a table '''
        ''' The table constant we are matching with.
         Right now, we have a hacky version of integer values which
         mimic an enum. Each integer value corresponds to a specific
         action PER table. The number of available integer values is
         constrained. '''
        ma_c_t = Datatype('ma_c_t')
        ma_c_t.declare('mk_ma_c_t', ('key_0', BitVecSort(32)),
                       ('action', IntSort()))
        ma = ma_c_t.create()

        @classmethod
        def table_match(cls, inouts):
            # The keys of the table are compared with the input keys.
            # In this case we are matching a single value
            # key = {
            #     key_0: exact @name("e") ;
            # }
            key_matches = []
            # Access the global variable key_0, which has been updated before
            c_t_key_0 = key_0
            # It is an exact match, so we use direct comparison
            key_matches.append(c_t_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

        # The possible table entries as constant
        m = Const('c_t_m', ma)
        # actions = {
        #     c_a_0();
        #     NoAction_0();
        # }
        actions = {
            "c_a_0": (1, (c_a_0, ())),
            "NoAction_0": (2, (NoAction_0, ())),
        }
        actions["default"] = (0, (NoAction_0, ()))

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
            sub_chain.append(c_t.apply)

            sub_chain.extend(func_chain)
            return step(sub_chain, inouts)
        # }
        sub_chain.append(block)

        def output_update(func_chain, inouts):
            rval = BitVecVal(0, 9)
            update = inouts.set("sm.egress_spec", rval)
            return step(func_chain, inouts, update)
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
    print(control_ingress_0(s, inouts))
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


# If(And(a(hdr6192_0) + a(hdr6192_0) == key_0(c_t_m)),
#    Xor(Implies(action(c_t_m) == 1,
#                inouts5688_2 ==
#                mk_inouts(mk_headers(mk_hdr(a(hdr6192_0),
#                                         a(hdr6192_0))),
#                          mk_meta,
#                          mk_standard_metadata_t(0))),
#        Implies(action(c_t_m) == 2,
#                inouts5688_2 ==
#                mk_inouts(mk_headers(mk_hdr(a(hdr6192_0),
#                                         a(hdr6192_0))),
#                          mk_meta,
#                          mk_standard_metadata_t(0)))),
#    inouts5688_2 ==
#    mk_inouts(mk_headers(mk_hdr(a(hdr6192_0), a(hdr6192_0))),
#              mk_meta,
#              mk_standard_metadata_t(0)))
