from p4z3_base import *

''' Model imports at the top of the p4 file '''
from v1model import *


z3_args = [
    ('dstAddr', BitVecSort(48)),
    ('srcAddr', BitVecSort(48)),
    ('etherType', BitVecSort(16))]

z3_reg.register_z3_type("ethernet_t", Header, z3_args)


z3_args = []
z3_reg.register_z3_type("metadata", Struct, z3_args)


z3_args = [('ethernet', z3_reg.reg["ethernet_t"])]
z3_reg.register_z3_type("headers", Struct, z3_args)


z3_args = [('hdr', z3_reg.reg["headers"]), ('meta', z3_reg.reg["metadata"]),
           ('standard_metadata', z3_reg.reg["standard_metadata_t"])]
z3_reg.register_z3_type("inouts", Struct, z3_args)


def control_ingress_0(s, inouts):
    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_1(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_2(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    # @name(".NoAction") action NoAction_0() {
    # }
    def on_miss_1(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    # @name(".NoAction") action NoAction_0() {
    # }
    def on_miss_2(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_eth_type(func_chain, inouts):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        # This updates an existing output variable so  we need a new version
        # The new constant is appended to the existing list of constants
        # Now we create the new version by using a data type constructor
        # The data type constructor uses the values from the previous
        # variable version, except for the update target.
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = BitVec(2, 16)
            expr = inouts.set("hdr.ethernet.etherType", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_eth_type_2(func_chain, inouts):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        # This updates an existing output variable so  we need a new version
        # The new constant is appended to the existing list of constants
        # Now we create the new version by using a data type constructor
        # The data type constructor uses the values from the previous
        # variable version, except for the update target.
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = BitVec(2, 16)
            expr = inouts.set("hdr.ethernet.etherType", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    class eth_dst(Table):

        ma_eth_dst = Datatype('ma_eth_dst')
        ma_eth_dst.declare('mk_ma_eth_dst',
                           ('key_0', BitVecSort(48)),
                           ('action', IntSort()))
        ma = ma_eth_dst.create()
        m = Const('eth_dst_m', ma)

        actions = {
            "on_miss_1": (1, (on_miss_1, ())),
            "set_eth_type": (2, (set_eth_type, ())),
        }
        actions["default"] = (0, (NoAction_1, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            eth_dst_key_0 = inouts.hdr.ethernet.dstAddr
            key_matches.append(eth_dst_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    class eth_src(Table):

        ma_eth_src = Datatype('ma_eth_src')
        ma_eth_src.declare('mk_ma_eth_src',
                           ('key_0', BitVecSort(48)),
                           ('action', IntSort()))
        ma = ma_eth_src.create()
        m = Const('eth_src_m', ma)

        actions = {
            "on_miss_2": (1, (on_miss_2, ())),
            "set_eth_type_2": (2, (set_eth_type_2, ()))
        }
        actions["default"] = (0, (NoAction_2, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            eth_dst_key_0 = inouts.hdr.ethernet.srcAddr
            key_matches.append(eth_dst_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    def apply(func_chain, inouts):
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        sub_chain = []

        sub_chain.append(eth_dst.apply)

        def switch_block(func_chain, inouts):
            cases = []
            switch = eth_dst.action_run(inouts)
            a = eth_dst.actions

            def case_block(func_chain, inouts):
                sub_chain = []

                sub_chain.append(eth_src.apply)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(
                switch == a["on_miss_1"][0],
                case_block(func_chain, inouts))
            cases.append(case)
            return And(*cases, step(func_chain, inouts))
        sub_chain.append(switch_block)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)
    # return the apply function as sequence of logic clauses
    return step(func_chain=[apply], inouts=inouts)


def control_ingress_1(s, inouts):
    ''' This is the initial version of the program. '''

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_1(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    # @name(".NoAction") action NoAction_0() {
    # }
    def NoAction_2(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    # @name(".NoAction") action NoAction_0() {
    # }
    def on_miss_1(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    # @name(".NoAction") action NoAction_0() {
    # }
    def on_miss_2(func_chain, inouts):
        ''' This is an action
            NoAction just returns the current header as is '''
        sub_chain = []

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_eth_type(func_chain, inouts):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        # This updates an existing output variable so  we need a new version
        # The new constant is appended to the existing list of constants
        # Now we create the new version by using a data type constructor
        # The data type constructor uses the values from the previous
        # variable version, except for the update target.
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = BitVec(2, 16)
            expr = inouts.set("hdr.ethernet.etherType", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    def set_eth_type_2(func_chain, inouts):
        ''' This is an action
            This action creates a new header type where b is set to a '''
        # This updates an existing output variable so  we need a new version
        # The new constant is appended to the existing list of constants
        # Now we create the new version by using a data type constructor
        # The data type constructor uses the values from the previous
        # variable version, except for the update target.
        sub_chain = []

        def output_update(func_chain, inouts):
            rval = BitVec(2, 16)
            expr = inouts.set("hdr.ethernet.etherType", rval)
            return step(func_chain, inouts, expr)
        sub_chain.append(output_update)

        sub_chain.extend(func_chain)
        return step(sub_chain, inouts)

    class eth_dst(Table):

        ma_eth_dst = Datatype('ma_eth_dst')
        ma_eth_dst.declare('mk_ma_eth_dst',
                           ('key_0', BitVecSort(48)),
                           ('action', IntSort()))
        ma = ma_eth_dst.create()
        m = Const('eth_dst_m', ma)

        actions = {
            "on_miss_1": (1, (on_miss_1, ())),
            "set_eth_type": (2, (set_eth_type, ())),
        }
        actions["default"] = (0, (NoAction_1, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            eth_dst_key_0 = inouts.hdr.ethernet.dstAddr
            key_matches.append(eth_dst_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    class eth_src(Table):

        ma_eth_src = Datatype('ma_eth_src')
        ma_eth_src.declare('mk_ma_eth_src',
                           ('key_0', BitVecSort(48)),
                           ('action', IntSort()))
        ma = ma_eth_src.create()
        m = Const('eth_src_m', ma)

        actions = {
            "on_miss_2": (1, (on_miss_2, ())),
            "set_eth_type_2": (2, (set_eth_type_2, ()))
        }
        actions["default"] = (0, (NoAction_2, ()))

        @classmethod
        def table_match(cls, inouts):

            key_matches = []
            eth_dst_key_0 = inouts.hdr.ethernet.srcAddr
            key_matches.append(eth_dst_key_0 == cls.ma.key_0(cls.m))
            return And(key_matches)

    def apply(func_chain, inouts):
        ''' The main function of the control plane. Each statement in this pipe
        is part of a list of functions. '''
        sub_chain = []

        sub_chain.append(eth_dst.apply)

        def switch_block(func_chain, inouts):
            cases = []
            switch = eth_dst.action_run(inouts)
            a = eth_dst.actions

            def case_block(func_chain, inouts):
                sub_chain = []

                sub_chain.append(eth_src.apply)

                sub_chain.extend(func_chain)
                return step(sub_chain, inouts)
            case = Implies(
                switch == a["on_miss_1"][0],
                case_block(func_chain, inouts))
            cases.append(case)

            return And(*cases, step(func_chain, inouts))
        sub_chain.append(switch_block)

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

    inouts = z3_reg.reg["INOUTS"]()
    bounds = [inouts.const]
    #out = control_ingress_1(s, inouts)
    # print("FINAL OUTPUT")
    # print(out)
    # exit(0)
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
