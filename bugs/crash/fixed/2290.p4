/*Invoking preprocessor
cpp -C -undef -nostdinc -x assembler-with-cpp  -Ip4_tv/p4c/build/p4include -D__TARGET_BMV2__ -Ip4_tv/p4c/build/p4include -Ip4_tv/p4c/build/p4include ./2290.p4i
ParseAnnotationBodies_0_ParseAnnotations
ParseAnnotationBodies_1_ClearTypeMap
FrontEnd_0_ParseAnnotationBodies
FrontEnd_1_PrettyPrint
FrontEnd_2_ValidateParsedProgram
FrontEnd_3_CreateBuiltins
FrontEnd_4_ResolveReferences
ConstantFolding_0_DoConstantFolding
FrontEnd_5_ConstantFolding
InstantiateDirectCalls_0_ResolveReferences
InstantiateDirectCalls_1_DoInstantiateCalls
FrontEnd_6_InstantiateDirectCalls
FrontEnd_7_ResolveReferences
Deprecated_0_ResolveReferences
Deprecated_1_CheckDeprecated
FrontEnd_8_Deprecated
FrontEnd_9_CheckNamedArgs
bugs/crash/fixed/2290.p4(16): [--Werror=type-error] error: Field s of header nested_header cannot have type header simple_header
    simple_header s;
                  ^
bugs/crash/fixed/2290.p4(11)
header simple_header {
       ^^^^^^^^^^^^^
In file: p4_tv/p4c/frontends/p4/typeChecking/typeChecker.cpp:564
[31mCompiler Bug[0m: Unexpected type <Type_Name>(1138) nested_header

running cc -E -C -undef -nostdinc -x assembler-with-cpp -I p4_tv/p4c/build/p4include -o ./2290.p4i bugs/crash/fixed/2290.p4
running p4_tv/p4c/build/p4c-bm2-ss -I p4_tv/p4c/build/p4include --p4v=16 -vvv -o ./2290.json ./2290.p4i --arch v1model

*/
#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}


header simple_header {
    bit<8>  a;
}

header nested_header {
    simple_header s;
}

struct Headers {
    ethernet_t eth_hdr;
    nested_header n;
}

struct Meta {
}


parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {

    apply {

    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {b.emit(h);} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

