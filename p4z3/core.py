from p4z3.callables import P4Method
from p4z3.base import gen_instance, P4Extern, P4Parameter, P4Member, z3
from p4z3.base import propagate_validity_bit, HeaderStackInstance
from p4z3.base import StructInstance

# extern packet_in {
#     /// Read a header from the packet into a fixed-sized header @hdr and advance the cursor.
#     /// May trigger error PacketTooShort or StackOutOfBounds.
#     /// @T must be a fixed-size header type
#     void extract<T>(out T hdr);
#     /// Read bits from the packet into a variable-sized header @variableSizeHeader
#     /// and advance the cursor.
#     /// @T must be a header containing exactly 1 varbit field.
#     /// May trigger errors PacketTooShort, StackOutOfBounds, or HeaderTooShort.
#     void extract<T>(out T variableSizeHeader,
#                     in bit<32> variableFieldSizeInBits);
#     /// Read bits from the packet without advancing the cursor.
#     /// @returns: the bits read from the packet.
#     /// T may be an arbitrary fixed-size type.
#     T lookahead<T>();
#     /// Advance the packet cursor by the specified number of bits.
#     void advance(in bit<32> sizeInBits);
#     /// @return packet length in bytes.  This method may be unavailable on
#     /// some target architectures.
#     bit<32> length();
# }


class packet_in(P4Extern):
    def __init__(self):
        self.name = "packet_in"
        z3_type = z3.Datatype(self.name)
        z3_type.declare(f"mk_{self.name}")
        self.z3_type = z3_type.create()
        self.type_params = {}
        self.type_context = {}
        # attach the methods
        self.locals = {}

        class extract(P4Method):
            def __init__(self):
                name = "extract"
                params = [P4Parameter(
                    "out", "hdr", "T", None), ]
                type_params = (None, ["T", ])
                super(extract, self).__init__(name, type_params, params)

            def __call__(self, p4_state, *args, **kwargs):
                for arg in args:
                    while isinstance(arg, P4Member):
                        member = arg.member
                        arg = arg.lval
                        if member == "next":
                            arg = p4_state.resolve_reference(arg)
                            if isinstance(arg, HeaderStackInstance):
                                arg.nextIndex += 1
                                arg.locals["lastIndex"] += 1
                                if arg.nextIndex > arg.locals["size"]:
                                    p4_state.parser_exception = True
                                    return

            def eval_callable(self, p4_state, merged_args, var_buffer):
                # initialize the local context of the function for execution
                if self.return_type is None:
                    return None

                return_instance = gen_instance(
                    p4_state, self.name, self.return_type)
                # a returned header may or may not be valid
                if isinstance(return_instance, StructInstance):
                    propagate_validity_bit(return_instance)
                return return_instance

        self.locals.setdefault("extract", []).append(extract())
        class extract(P4Method):

            def __init__(self):
                name = "extract"
                params = [
                    P4Parameter("out", "variableSizeHeader", "T", None),
                    P4Parameter("in", "variableFieldSizeInBits", z3.BitVecSort(32), None), ]
                type_params = (None, ["T", ])
                super(extract, self).__init__(name, type_params, params)

            def __call__(self, p4_state, *args, **kwargs):
                for arg in args:
                    while isinstance(arg, P4Member):
                        member = arg.member
                        arg = arg.lval
                        if member == "next":
                            arg = p4_state.resolve_reference(arg)
                            if isinstance(arg, HeaderStackInstance):
                                arg.nextIndex += 1
                                arg.locals["lastIndex"] += 1
                                if arg.nextIndex > arg.locals["size"]:
                                    p4_state.parser_exception = True
                                    return

            def eval_callable(self, p4_state, merged_args, var_buffer):
                # initialize the local context of the function for execution
                if self.return_type is None:
                    return None

                return_instance = gen_instance(
                    p4_state, self.name, self.return_type)
                # a returned header may or may not be valid
                if isinstance(return_instance, StructInstance):
                    propagate_validity_bit(return_instance)
                return return_instance

        self.locals.setdefault("extract", []).append(extract())

        class lookahead(P4Method):

            def __init__(self):
                name = "lookahead"
                type_params = ("T", ["T", ])
                params = []
                super(lookahead, self).__init__(name, type_params, params)

        self.locals.setdefault("lookahead", []).append(lookahead())
