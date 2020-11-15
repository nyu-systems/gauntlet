/*Invoking preprocessor
cpp -C -undef -nostdinc -x assembler-with-cpp  -Ip4c/build/p4include bugs/crash/same_name_crash.p4
FrontEnd_0_P4V1::getV1ModelVersion
ParseAnnotationBodies_0_ParseAnnotations
ParseAnnotationBodies_1_ClearTypeMap
FrontEnd_1_ParseAnnotationBodies
FrontEnd_2_PrettyPrint
FrontEnd_3_ValidateParsedProgram
FrontEnd_4_CreateBuiltins
bugs/crash/same_name_crash.p4(24): [--Wwarn=shadow] warning: 'h' shadows 'h'
        Headers h = h;
        ^^^^^^^^^^^^^^
bugs/crash/same_name_crash.p4(22)
control ingress(inout Headers h) {
                              ^
FrontEnd_5_ResolveReferences
ConstantFolding_0_DoConstantFolding
FrontEnd_6_ConstantFolding
InstantiateDirectCalls_0_ResolveReferences
InstantiateDirectCalls_1_DoInstantiateCalls
FrontEnd_7_InstantiateDirectCalls
FrontEnd_8_ResolveReferences
Deprecated_0_ResolveReferences
Deprecated_1_CheckDeprecated
FrontEnd_9_Deprecated
FrontEnd_10_CheckNamedArgs
In file: p4c/frontends/p4/typeChecking/typeChecker.cpp:168
[31mCompiler Bug[0m: bugs/crash/same_name_crash.p4(24): Could not find type of <Declaration_Variable>(238) h/34 Headers h = h;
        Headers h = h;
        ^^^^^^^^^^^^^^*/



#include <core.p4>
header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h) {
    apply {
        Headers h = h;
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

