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
        HeaderType("ethernet_t", z3_reg, z3_args=[("dst_addr", z3.BitVecSort(48)), ("src_addr", z3.BitVecSort(48)), ("eth_type", z3.BitVecSort(16)), ])
    )
    z3_reg.declare_global(
        HeaderType("H", z3_reg, z3_args=[("a", z3.BitVecSort(8)), ])
    )
    z3_reg.declare_global(
        StructType("Headers", z3_reg, z3_args=[("eth_hdr", "ethernet_t"), ("h", "H"), ])
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Parser(
            name="p",
            type_params=[],
            params=[
                P4Parameter("none", "pkt", "packet_in", None),
                P4Parameter("out", "hdr", "Headers", None),],
            const_params=[],
            local_decls=[],
            body=ParserTree([
                ParserState(name="start", select="accept",
                components=[
                MethodCallStmt(MethodCallExpr(P4Member("pkt", "extract"), ["ethernet_t", ], P4Member("hdr", "eth_hdr"), )),
                MethodCallStmt(MethodCallExpr(P4Member("pkt", "extract"), ["H", ], P4Member("hdr", "h"), )),                ]),
                ])
))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Control(
            name="ingress",
            type_params=[],
            params=[
                P4Parameter("inout", "h", "Headers", None),],
            const_params=[],
            body=BlockStatement([
                BlockStatement([
                    AssignmentStatement("tmp_0_eth_hdr", P4Member("h", "eth_hdr")),
                    AssignmentStatement("tmp_0_h", P4Member("h", "h")),]
                ),
                MethodCallStmt(MethodCallExpr("reset_action", [], )),
                BlockStatement([
                    AssignmentStatement(P4Member("h", "eth_hdr"), "tmp_0_eth_hdr"),
                    AssignmentStatement(P4Member("h", "h"), "tmp_0_h"),]
                ),]
            ),
            local_decls=[
ValueDeclaration("tmp_eth_hdr", None, z3_type="ethernet_t"), 
ValueDeclaration("tmp_h", None, z3_type="H"), 
ValueDeclaration("tmp_0_eth_hdr", None, z3_type="ethernet_t"), 
ValueDeclaration("tmp_0_h", None, z3_type="H"), 
ValueDeclaration("out_h_eth_hdr", None, z3_type="ethernet_t"), 
ValueDeclaration("out_h_h", None, z3_type="H"), 
ValueDeclaration("inout_h_eth_hdr", None, z3_type="ethernet_t"), 
ValueDeclaration("inout_h_h", None, z3_type="H"), 
P4Declaration("reset_action", P4Action("reset_action", params=[],                 body=BlockStatement([
                    BlockStatement([
                        AssignmentStatement("inout_h_eth_hdr", "tmp_0_eth_hdr"),
                        AssignmentStatement("inout_h_h", "tmp_0_h"),]
                    ),
                    AssignmentStatement(P4Member("inout_h_eth_hdr", "eth_type"), P4Member("out_h_eth_hdr", "eth_type")),
                    BlockStatement([
                        AssignmentStatement("tmp_eth_hdr", "out_h_eth_hdr"),
                        AssignmentStatement("tmp_h", "out_h_h"),]
                    ),
                    BlockStatement([
                        AssignmentStatement("tmp_0_eth_hdr", "inout_h_eth_hdr"),
                        AssignmentStatement("tmp_0_h", "inout_h_h"),]
                    ),]
                )                )), ]
        ))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4ParserType("Parser", params=[
            P4Parameter("none", "b", "packet_in", None),
            P4Parameter("out", "hdr", "Headers", None),], type_params=[]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4ControlType("Ingress", params=[
            P4Parameter("inout", "hdr", "Headers", None),], type_params=[]))
    )
    z3_reg.declare_global(
        ControlDeclaration(P4Package(z3_reg, "top", params=[
            P4Parameter("none", "p", "Parser", None),
            P4Parameter("none", "ig", "Ingress", None),],type_params=[]))
    )
    z3_reg.declare_global(
        InstanceDeclaration("main", "top", ConstCallExpr("p", ), ConstCallExpr("ingress", ), )
    )
    var = z3_reg.get_main_function()
    return var if isinstance(var, P4Package) else None
