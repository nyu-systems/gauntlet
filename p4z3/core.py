# from p4z3.callables import P4Method
# from p4z3.base import gen_instance, P4Extern, P4Parameter, P4Member, z3
# from p4z3.base import propagate_validity_bit, HeaderStackInstance
# from p4z3.base import StructInstance
# from p4z3.callables import merge_parameters, save_variables, resolve_type
# from p4z3.base import merge_attrs, P4Context

# '''
#  extern packet_in {
#     /// Read a header from the packet into a fixed-sized header @hdr
#     /// and advance the cursor.
#     /// May trigger error PacketTooShort or StackOutOfBounds.
#     /// @T must be a fixed-size header type
#     void extract<T>(out T hdr);
#     /// Read bits from the packet into a variable-sized header
#     /// @variableSizeHeader and advance the cursor.
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
# '''


# class packet_in(P4Extern):
#     def __init__(self):
#         super(packet_in, self).__init__(
#             "packet_in", type_params={}, methods=[])

#         # attach the methods
#         self.locals = {}

#         # EXTRACT #

#         class extract_1(P4Method):
#             def __call__(self, p4_state, *args, **kwargs):
#                 merged_args = merge_parameters(self.params, *args, **kwargs)

#                 # resolve the inputs *before* we bind types
#                 method_args = {}
#                 for param_name, arg in merged_args.items():
#                     # we need to resolve "in" too because of side-effects
#                     arg_expr = p4_state.resolve_expr(arg.p4_val)
#                     method_args[param_name] = (
#                         arg.mode, arg.p4_val, arg_expr, arg.p4_type)

#                 # apply the local and parent extern type contexts
#                 local_context = {}
#                 for type_name, p4_type in self.extern_context.items():
#                     local_context[type_name] = resolve_type(p4_state, p4_type)
#                 for type_name, p4_type in self.type_context.items():
#                     local_context[type_name] = resolve_type(p4_state, p4_type)
#                 p4_state.type_contexts.append(local_context)

#                 # assign symbolic values to the inputs that are inout and out
#                 self.assign_values(p4_state, method_args)

#                 # execute the return expression within the new type environment
#                 expr = self.eval_callable(p4_state, merged_args, {})

#                 # cleanup and return the value
#                 p4_state.type_contexts.pop()
#                 self.call_counter += 1
#                 # for arg in args:
#                 #     while isinstance(arg, P4Member):
#                 #         member = arg.member
#                 #         arg = arg.lval
#                 #         if member == "next":
#                 #             arg = p4_state.resolve_reference(arg)
#                 #             if isinstance(arg, HeaderStackInstance):
#                 #                 arg.nextIndex += 1
#                 #                 arg.locals["lastIndex"] += 1
#                 #                 if arg.nextIndex > arg.locals["size"]:
#                 #                     p4_state.parser_exception = True
#                 #                     return
#                 return expr

#         extract_1_var = extract_1(name="extract",
#                                   params=[P4Parameter(
#                                       "out", "hdr", "T", None), ],
#                                   type_params=(None, ["T", ]))

#         extract_2_var = extract_1(name="extract",
#                                   params=[
#                                       P4Parameter("out", "variableSizeHeader",
#                                                   "T", None),
#                                       P4Parameter("in",
#                                                   "variableFieldSizeInBits",
#                                                   z3.BitVecSort(32), None),
#                                   ], type_params=(None, ["T", ]))
#         self.locals.setdefault("extract", []).append(extract_1_var)
#         self.locals.setdefault("extract", []).append(extract_2_var)

#         # LOOKAHEAD #

#         lookahead_var = P4Method(name="lookahead",
#                                  params=[],
#                                  type_params=("T", ["T", ]))
#         self.locals.setdefault("lookahead", []).append(lookahead_var)

#         # LENGTH #

#         self.locals["length"] = z3.BitVec(f"{self.name}_length", 32)

#         # ADVANCE #
#         class advance(P4Method):

#             def eval_callable(self, p4_state, merged_args, var_buffer):

#                 self.locals["length"] += merged_args["sizeInBits"]

#         advance_var = advance(name="advance",
#                               params=[P4Parameter("in", "sizeInBits",
#                                                   z3.BitVecSort(32), None)],
#                               type_params=(None, []))
#         self.locals.setdefault("extract", []).append(advance_var)


core_externs = {}
