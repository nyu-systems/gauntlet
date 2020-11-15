from p4z3.callables import P4Method
from p4z3.base import P4Extern, P4Parameter, z3
from p4z3.base import log, P4Member, HeaderStackInstance
from p4z3.callables import merge_parameters, resolve_type
from p4z3.parser import ParserException

'''
 extern packet_in {
    /// Read a header from the packet into a fixed-sized header @hdr
    /// and advance the cursor.
    /// May trigger error PacketTooShort or StackOutOfBounds.
    /// @T must be a fixed-size header type
    void extract<T>(out T hdr);
    /// Read bits from the packet into a variable-sized header
    /// @variableSizeHeader and advance the cursor.
    /// @T must be a header containing exactly 1 varbit field.
    /// May trigger errors PacketTooShort, StackOutOfBounds, or HeaderTooShort.
    void extract<T>(out T variableSizeHeader,
                    in bit<32> variableFieldSizeInBits);
    /// Read bits from the packet without advancing the cursor.
    /// @returns: the bits read from the packet.
    /// T may be an arbitrary fixed-size type.
    T lookahead<T>();
    /// Advance the packet cursor by the specified number of bits.
    void advance(in bit<32> sizeInBits);
    /// @return packet length in bytes.  This method may be unavailable on
    /// some target architectures.
    bit<32> length();
}
'''


def detect_hdr_stack_next(p4_state, hdr_ref):
    while isinstance(hdr_ref, P4Member):
        member = hdr_ref.member
        hdr_ref = hdr_ref.lval
        if member == "next":
            hdr_ref = p4_state.resolve_reference(hdr_ref)
            if isinstance(hdr_ref, HeaderStackInstance):
                return hdr_ref
    return None


class packet_in(P4Extern):
    def __init__(self):
        super(packet_in, self).__init__(
            "packet_in", type_params={}, methods=[])

        self.pkt_cursor = z3.BitVecVal(0, 32)
        # attach the methods
        self.locals = {}

        # EXTRACT #
        class extract_1(P4Method):
            hdr_param_name = "hdr"

            def extract_hdr(self, p4_state, merged_args):
                hdr = merged_args[self.hdr_param_name].p4_val
                context = p4_state.current_context()
                # apply the local and parent extern type contexts
                for type_name, p4_type in self.extern_context.items():
                    context.add_type(type_name, resolve_type(p4_state, p4_type))
                for type_name, p4_type in self.type_context.items():
                    context.add_type(type_name, resolve_type(p4_state, p4_type))

                # advance the header index if a next field has been accessed
                hdr_stack = detect_hdr_stack_next(p4_state, hdr)
                if hdr_stack:
                    compare = hdr_stack.locals["nextIndex"] >= hdr_stack.locals["size"]
                    if z3.simplify(compare) == z3.BoolVal(True):
                        raise ParserException("Index out of bounds!")

                # grab the hdr value
                hdr_expr = p4_state.resolve_expr(hdr)

                hdr_expr.activate()
                bind_const = z3.Const(
                    f"{self.name}_{self.hdr_param_name}", hdr_expr.z3_type)
                hdr_expr.bind(bind_const)

                # advance the stack, if it exists
                if hdr_stack:
                    hdr_stack.locals["lastIndex"] = hdr_stack.locals["nextIndex"]
                    hdr_stack.locals["nextIndex"] += 1
                self.call_counter += 1

            def __call__(self, p4_state, *args, **kwargs):
                merged_args = merge_parameters(self.params, *args, **kwargs)
                # this means default expressions have been used, no input
                if not merged_args:
                    return
                self.extract_hdr(p4_state, merged_args)

        class extract_2(extract_1):
            hdr_param_name = "variableSizeHeader"

            def __call__(self, p4_state, *args, **kwargs):
                merged_args = merge_parameters(self.params, *args, **kwargs)
                # this means default expressions have been used, no input
                if not merged_args:
                    return
                self.extract_hdr(p4_state, merged_args)
                field_size = p4_state.resolve_expr(
                    merged_args["variableFieldSizeInBits"].p4_val)
                # self.pkt_cursor += field_size

        extract_1_var = extract_1(name="extract",
                                  params=[P4Parameter(
                                      "out", "hdr", "T", None), ],
                                  type_params=(None, ["T", ]))

        extract_2_var = extract_2(name="extract",
                                  params=[
                                      P4Parameter("out", "variableSizeHeader",
                                                  "T", None),
                                      P4Parameter("in",
                                                  "variableFieldSizeInBits",
                                                  z3.BitVecSort(32), None),
                                  ], type_params=(None, ["T", ]))
        self.locals.setdefault("extract", []).append(extract_1_var)
        self.locals.setdefault("extract", []).append(extract_2_var)

        # LOOKAHEAD #
        lookahead_var = P4Method(name="lookahead",
                                 params=[],
                                 type_params=("T", ["T", ]))
        self.locals.setdefault("lookahead", []).append(lookahead_var)

        # LENGTH #
        self.locals["length"] = z3.BitVec(f"{self.name}_length", 32)

        # ADVANCE #
        class advance(P4Method):

            def eval_callable(self, p4_state, merged_args, var_buffer):
                # self.pkt_cursor += merged_args["sizeInBits"]
                pass

        advance_var = advance(name="advance",
                              params=[P4Parameter("in", "sizeInBits",
                                                  z3.BitVecSort(32), None)],
                              type_params=(None, []))
        self.locals.setdefault("advance", []).append(advance_var)


core_externs = {"packet_in": packet_in()}
