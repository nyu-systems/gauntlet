from p4z3.callables import P4Method
from p4z3.base import P4Extern, z3, P4Parameter
from p4z3.base import P4ComplexInstance, HeaderStackInstance


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
        self.members = []
        self.z3_type = z3_type.create()
        self.const = z3.Const(self.name, self.z3_type)
        self.locals = {}
        # simple fix for now until I know how to initialize params for externs
        self.params = {}
        self.type_params = []

        class extract(P4Method):

            def __init__(self):
                self.name = "extract"
                self.params = [P4Parameter(
                    "out", "hdr", z3.SortRef("T"), None), ]
                self.type_params = (None, [z3.SortRef("T"), ])
                self.call_counter = 0
                self.locals = {}

            def eval_callable(self, p4_state, merged_args, var_buffer):
                log.info("ASDASDASD")
                # initialize the local context of the function for execution
                if self.return_type is None:
                    return None
                # methods can return values, we need to generate a new constant
                # we generate the name based on the input arguments
                # var_name = ""
                # for arg in merged_args.values():
                #     arg = p4_state.resolve_expr(arg.p4_val)
                #     # fold runtime-known values
                #     if isinstance(arg, z3.AstRef):
                #         arg = z3.simplify(arg)
                #     # elif isinstance(arg, list):
                #     #     for idx, member in enumerate(arg):
                #     #         arg[idx] = z3.simplify(member)

                #     # Because we do not know what the extern is doing
                #     # we initiate a new z3 const and
                #     # just overwrite all reference types
                #     # input arguments influence the output behavior
                #     # add the input value to the return constant
                #     var_name += str(arg)
                # If we return something, instantiate the type and return it
                # we merge the name
                # FIXME: We do not consider call order
                # and assume that externs are stateless
                return_instance = gen_instance(self.name, self.return_type)
                # a returned header may or may not be valid
                if isinstance(return_instance, P4ComplexInstance):
                    return_instance.propagate_validity_bit()
                return return_instance

        self.locals["extract"] = extract()

        # dummy
        self.valid = False


core_externs = {"packet_in": packet_in()}
