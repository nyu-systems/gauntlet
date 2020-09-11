from p4z3 import *



def p4_program(z3_reg):
    z3_reg.declare_global(
        Enum( "error", ["NoError", "PacketTooShort", "NoMatch", "StackOutOfBounds", "HeaderTooShort", "ParserTimeout", "ParserInvalidArgument", ])
    )
    z3_reg.declare_global(
        P4Extern("packet_in", type_params=[], methods=[P4Declaration("extract", P4Method("extract", type_params=(None, [
            "T",]), params=[
            P4Parameter("out", "hdr", "T", None),])), P4Declaration("extract", P4Method("extract", type_params=(None, [
            "T",]), params=[
            P4Parameter("out", "variableSizeHeader", "T", None),
            P4Parameter("in", "variableFieldSizeInBits", z3.BitVecSort(32), None),])), P4Declaration("lookahead", P4Method("lookahead", type_params=("T", [
            "T",]), params=[])), P4Declaration("advance", P4Method("advance", type_params=(None, []), params=[
            P4Parameter("in", "sizeInBits", z3.BitVecSort(32), None),])), P4Declaration("length", P4Method("length", type_params=(z3.BitVecSort(32), []), params=[])), ])
    )
    z3_reg.declare_global(
        P4Extern("packet_out", type_params=[], methods=[P4Declaration("emit", P4Method("emit", type_params=(None, [
            "T",]), params=[
            P4Parameter("in", "hdr", "T", None),])), ])
    )
    z3_reg.declare_global(
        P4Declaration("verify", P4Method("verify", type_params=(None, []), params=[
            P4Parameter("in", "check", z3.BoolSort(), None),
            P4Parameter("in", "toSignal", "error", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("NoAction", P4Action("NoAction", params=[],         body=BlockStatement([]
        )        ))
    )
    z3_reg.declare_global(
        P4Declaration("match_kind", ["exact", "ternary", "lpm", ])
    )
    z3_reg.declare_global(
        P4Declaration("match_kind", ["range", "optional", "selector", ])
    )
    z3_reg.declare_global(
        ValueDeclaration("__v1model_version", 20180101, z3_type=z3.BitVecSort(32))
    )
    z3_reg.declare_global(
        StructType("standard_metadata_t", z3_reg, z3_args=[("ingress_port", z3.BitVecSort(9)), ("egress_spec", z3.BitVecSort(9)), ("egress_port", z3.BitVecSort(9)), ("instance_type", z3.BitVecSort(32)), ("packet_length", z3.BitVecSort(32)), ("enq_timestamp", z3.BitVecSort(32)), ("enq_qdepth", z3.BitVecSort(19)), ("deq_timedelta", z3.BitVecSort(32)), ("deq_qdepth", z3.BitVecSort(19)), ("ingress_global_timestamp", z3.BitVecSort(48)), ("egress_global_timestamp", z3.BitVecSort(48)), ("mcast_grp", z3.BitVecSort(16)), ("egress_rid", z3.BitVecSort(16)), ("checksum_error", z3.BitVecSort(1)), ("parser_error", "error"), ("priority", z3.BitVecSort(3)), ])
    )
    z3_reg.declare_global(
        Enum( "CounterType", ["packets", "bytes", "packets_and_bytes", ])
    )
    z3_reg.declare_global(
        Enum( "MeterType", ["packets", "bytes", ])
    )
    z3_reg.declare_global(
        P4Extern("counter", type_params=[], methods=[P4Declaration("counter", P4Method("counter", type_params=(None, []), params=[
            P4Parameter("none", "size", z3.BitVecSort(32), None),
            P4Parameter("none", "type", "CounterType", None),])), P4Declaration("count", P4Method("count", type_params=(None, []), params=[
            P4Parameter("in", "index", z3.BitVecSort(32), None),])), ])
    )
    z3_reg.declare_global(
        P4Extern("direct_counter", type_params=[], methods=[P4Declaration("direct_counter", P4Method("direct_counter", type_params=(None, []), params=[
            P4Parameter("none", "type", "CounterType", None),])), P4Declaration("count", P4Method("count", type_params=(None, []), params=[])), ])
    )
    z3_reg.declare_global(
        P4Extern("meter", type_params=[], methods=[P4Declaration("meter", P4Method("meter", type_params=(None, []), params=[
            P4Parameter("none", "size", z3.BitVecSort(32), None),
            P4Parameter("none", "type", "MeterType", None),])), P4Declaration("execute_meter", P4Method("execute_meter", type_params=(None, [
            "T",]), params=[
            P4Parameter("in", "index", z3.BitVecSort(32), None),
            P4Parameter("out", "result", "T", None),])), ])
    )
    z3_reg.declare_global(
        P4Extern("direct_meter", type_params=[
            "T",], methods=[P4Declaration("direct_meter", P4Method("direct_meter", type_params=(None, []), params=[
            P4Parameter("none", "type", "MeterType", None),])), P4Declaration("read", P4Method("read", type_params=(None, []), params=[
            P4Parameter("out", "result", "T", None),])), ])
    )
    z3_reg.declare_global(
        P4Extern("register", type_params=[
            "T",], methods=[P4Declaration("register", P4Method("register", type_params=(None, []), params=[
            P4Parameter("none", "size", z3.BitVecSort(32), None),])), P4Declaration("read", P4Method("read", type_params=(None, []), params=[
            P4Parameter("out", "result", "T", None),
            P4Parameter("in", "index", z3.BitVecSort(32), None),])), P4Declaration("write", P4Method("write", type_params=(None, []), params=[
            P4Parameter("in", "index", z3.BitVecSort(32), None),
            P4Parameter("in", "value", "T", None),])), ])
    )
    z3_reg.declare_global(
        P4Extern("action_profile", type_params=[], methods=[P4Declaration("action_profile", P4Method("action_profile", type_params=(None, []), params=[
            P4Parameter("none", "size", z3.BitVecSort(32), None),])), ])
    )
    z3_reg.declare_global(
        P4Declaration("random", P4Method("random", type_params=(None, [
            "T",]), params=[
            P4Parameter("out", "result", "T", None),
            P4Parameter("in", "lo", "T", None),
            P4Parameter("in", "hi", "T", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("digest", P4Method("digest", type_params=(None, [
            "T",]), params=[
            P4Parameter("in", "receiver", z3.BitVecSort(32), None),
            P4Parameter("in", "data", "T", None),]))
    )
    z3_reg.declare_global(
        Enum( "HashAlgorithm", ["crc32", "crc32_custom", "crc16", "crc16_custom", "random", "identity", "csum16", "xor16", ])
    )
    z3_reg.declare_global(
        P4Declaration("mark_to_drop", P4Method("mark_to_drop", type_params=(None, []), params=[]))
    )
    z3_reg.declare_global(
        P4Declaration("mark_to_drop", P4Method("mark_to_drop", type_params=(None, []), params=[
            P4Parameter("inout", "standard_metadata", "standard_metadata_t", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("hash", P4Method("hash", type_params=(None, [
            "O",
            "T",
            "D",
            "M",]), params=[
            P4Parameter("out", "result", "O", None),
            P4Parameter("in", "algo", "HashAlgorithm", None),
            P4Parameter("in", "base", "T", None),
            P4Parameter("in", "data", "D", None),
            P4Parameter("in", "max", "M", None),]))
    )
    z3_reg.declare_global(
        P4Extern("action_selector", type_params=[], methods=[P4Declaration("action_selector", P4Method("action_selector", type_params=(None, []), params=[
            P4Parameter("none", "algorithm", "HashAlgorithm", None),
            P4Parameter("none", "size", z3.BitVecSort(32), None),
            P4Parameter("none", "outputWidth", z3.BitVecSort(32), None),])), ])
    )
    z3_reg.declare_global(
        Enum( "CloneType", ["I2E", "E2E", ])
    )
    z3_reg.declare_global(
        P4Extern("Checksum16", type_params=[], methods=[P4Declaration("Checksum16", P4Method("Checksum16", type_params=(None, []), params=[])), P4Declaration("get", P4Method("get", type_params=(z3.BitVecSort(16), [
            "D",]), params=[
            P4Parameter("in", "data", "D", None),])), ])
    )
    z3_reg.declare_global(
        P4Declaration("verify_checksum", P4Method("verify_checksum", type_params=(None, [
            "T",
            "O",]), params=[
            P4Parameter("in", "condition", z3.BoolSort(), None),
            P4Parameter("in", "data", "T", None),
            P4Parameter("in", "checksum", "O", None),
            P4Parameter("none", "algo", "HashAlgorithm", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("update_checksum", P4Method("update_checksum", type_params=(None, [
            "T",
            "O",]), params=[
            P4Parameter("in", "condition", z3.BoolSort(), None),
            P4Parameter("in", "data", "T", None),
            P4Parameter("inout", "checksum", "O", None),
            P4Parameter("none", "algo", "HashAlgorithm", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("verify_checksum_with_payload", P4Method("verify_checksum_with_payload", type_params=(None, [
            "T",
            "O",]), params=[
            P4Parameter("in", "condition", z3.BoolSort(), None),
            P4Parameter("in", "data", "T", None),
            P4Parameter("in", "checksum", "O", None),
            P4Parameter("none", "algo", "HashAlgorithm", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("update_checksum_with_payload", P4Method("update_checksum_with_payload", type_params=(None, [
            "T",
            "O",]), params=[
            P4Parameter("in", "condition", z3.BoolSort(), None),
            P4Parameter("in", "data", "T", None),
            P4Parameter("inout", "checksum", "O", None),
            P4Parameter("none", "algo", "HashAlgorithm", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("resubmit", P4Method("resubmit", type_params=(None, [
            "T",]), params=[
            P4Parameter("in", "data", "T", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("recirculate", P4Method("recirculate", type_params=(None, [
            "T",]), params=[
            P4Parameter("in", "data", "T", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("clone", P4Method("clone", type_params=(None, []), params=[
            P4Parameter("in", "type", "CloneType", None),
            P4Parameter("in", "session", z3.BitVecSort(32), None),]))
    )
    z3_reg.declare_global(
        P4Declaration("clone3", P4Method("clone3", type_params=(None, [
            "T",]), params=[
            P4Parameter("in", "type", "CloneType", None),
            P4Parameter("in", "session", z3.BitVecSort(32), None),
            P4Parameter("in", "data", "T", None),]))
    )
    z3_reg.declare_global(
        P4Declaration("truncate", P4Method("truncate", type_params=(None, []), params=[
            P4Parameter("in", "length", z3.BitVecSort(32), None),]))
    )
    z3_reg.declare_global(
        P4Declaration("assert", P4Method("assert", type_params=(None, []), params=[
            P4Parameter("in", "check", z3.BoolSort(), None),]))
    )
    z3_reg.declare_global(
        P4Declaration("assume", P4Method("assume", type_params=(None, []), params=[
            P4Parameter("in", "check", z3.BoolSort(), None),]))
    )
    z3_reg.declare_global(
        P4Declaration("log_msg", P4Method("log_msg", type_params=(None, []), params=[
            P4Parameter("none", "msg", z3.StringSort(), None),]))
    )
    z3_reg.declare_global(
        P4Declaration("log_msg", P4Method("log_msg", type_params=(None, [
            "T",]), params=[
            P4Parameter("none", "msg", z3.StringSort(), None),
            P4Parameter("in", "data", "T", None),]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4ParserType("Parser", params=[
            P4Parameter("none", "b", "packet_in", None),
            P4Parameter("out", "parsedHdr", "H", None),
            P4Parameter("inout", "meta", "M", None),
            P4Parameter("inout", "standard_metadata", "standard_metadata_t", None),], type_params=[
            "H",
            "M",]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4ControlType("VerifyChecksum", params=[
            P4Parameter("inout", "hdr", "H", None),
            P4Parameter("inout", "meta", "M", None),], type_params=[
            "H",
            "M",]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4ControlType("Ingress", params=[
            P4Parameter("inout", "hdr", "H", None),
            P4Parameter("inout", "meta", "M", None),
            P4Parameter("inout", "standard_metadata", "standard_metadata_t", None),], type_params=[
            "H",
            "M",]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4ControlType("Egress", params=[
            P4Parameter("inout", "hdr", "H", None),
            P4Parameter("inout", "meta", "M", None),
            P4Parameter("inout", "standard_metadata", "standard_metadata_t", None),], type_params=[
            "H",
            "M",]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4ControlType("ComputeChecksum", params=[
            P4Parameter("inout", "hdr", "H", None),
            P4Parameter("inout", "meta", "M", None),], type_params=[
            "H",
            "M",]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4ControlType("Deparser", params=[
            P4Parameter("none", "b", "packet_out", None),
            P4Parameter("in", "hdr", "H", None),], type_params=[
            "H",]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Package(z3_reg, "V1Switch", params=[
            P4Parameter("none", "p", TypeSpecializer("Parser", "H", "M", ), None),
            P4Parameter("none", "vr", TypeSpecializer("VerifyChecksum", "H", "M", ), None),
            P4Parameter("none", "ig", TypeSpecializer("Ingress", "H", "M", ), None),
            P4Parameter("none", "eg", TypeSpecializer("Egress", "H", "M", ), None),
            P4Parameter("none", "ck", TypeSpecializer("ComputeChecksum", "H", "M", ), None),
            P4Parameter("none", "dep", TypeSpecializer("Deparser", "H", ), None),],type_params=[
            "H",
            "M",]))
    )
    z3_reg.declare_global(
        HeaderType("ethernet_t", z3_reg, z3_args=[("dst_addr", z3.BitVecSort(48)), ("src_addr", z3.BitVecSort(48)), ("eth_type", z3.BitVecSort(16)), ])
    )
    z3_reg.declare_global(
        StructType("Meta", z3_reg, z3_args=[])
    )
    z3_reg.declare_global(
        StructType("Headers", z3_reg, z3_args=[("eth_hdr", "ethernet_t"), ])
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Parser(
            name="p",
            type_params=[],
            params=[
                P4Parameter("none", "pkt", "packet_in", None),
                P4Parameter("out", "hdr", "Headers", None),
                P4Parameter("inout", "m", "Meta", None),
                P4Parameter("inout", "sm", "standard_metadata_t", None),],
            const_params=[],
            local_decls=[],
            body=ParserTree([
                ParserState(name="start", select="accept",
                components=[
                MethodCallStmt(MethodCallExpr(P4Member("pkt", "extract"), ["ethernet_t", ], P4Member("hdr", "eth_hdr"), )),                ]),
                ])
))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Control(
            name="ingress",
            type_params=[],
            params=[
                P4Parameter("inout", "hdr", "Headers", None),
                P4Parameter("inout", "m", "Meta", None),
                P4Parameter("inout", "sm", "standard_metadata_t", None),],
            const_params=[],
            body=BlockStatement([
                BlockStatement([]
                ),
                MethodCallStmt(MethodCallExpr(P4Member("simple_tbl_0", "apply"), [], )),]
            ),
            local_decls=[
P4Declaration("set_mac_0", P4Action("set_mac", params=[
                    P4Parameter("none", "dst_mac", z3.BitVecSort(48), None),],                 body=BlockStatement([
                    AssignmentStatement(P4Member(P4Member("hdr", "eth_hdr"), "dst_addr"), "dst_mac"),]
                )                )), 
P4Declaration("simple_tbl_0", P4Table("simple_tbl", key=[(P4Member(P4Member("hdr", "eth_hdr"), "src_addr"), "exact"), ], actions=[MethodCallExpr("NoAction", [], ), MethodCallExpr("set_mac_0", [], ), ], default_action=MethodCallExpr("NoAction", [], ), )), ]
        ))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Control(
            name="vrfy",
            type_params=[],
            params=[
                P4Parameter("inout", "h", "Headers", None),
                P4Parameter("inout", "m", "Meta", None),],
            const_params=[],
            body=BlockStatement([]
            ),
            local_decls=[]
        ))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Control(
            name="update",
            type_params=[],
            params=[
                P4Parameter("inout", "h", "Headers", None),
                P4Parameter("inout", "m", "Meta", None),],
            const_params=[],
            body=BlockStatement([]
            ),
            local_decls=[]
        ))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Control(
            name="egress",
            type_params=[],
            params=[
                P4Parameter("inout", "h", "Headers", None),
                P4Parameter("inout", "m", "Meta", None),
                P4Parameter("inout", "sm", "standard_metadata_t", None),],
            const_params=[],
            body=BlockStatement([]
            ),
            local_decls=[]
        ))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Control(
            name="deparser",
            type_params=[],
            params=[
                P4Parameter("none", "b", "packet_out", None),
                P4Parameter("in", "h", "Headers", None),],
            const_params=[],
            body=BlockStatement([
                MethodCallStmt(MethodCallExpr(P4Member("b", "emit"), ["Headers", ], "h", )),]
            ),
            local_decls=[]
        ))
    )
    z3_reg.declare_global(
        InstanceDeclaration("main", TypeSpecializer("V1Switch", "Headers", "Meta", ), ConstCallExpr("p", ), ConstCallExpr("vrfy", ), ConstCallExpr("ingress", ), ConstCallExpr("egress", ), ConstCallExpr("update", ), ConstCallExpr("deparser", ), )
    )
    var = z3_reg.get_main_function()
    return var if isinstance(var, P4Package) else None
