/*Invoking preprocessor
cpp -C -undef -nostdinc -x assembler-with-cpp  -D__TARGET_BMV2__ -Ip4_tv/p4c/build/backends/bmv2/p4include bugs/crash/fixed/2356.p4
FrontEnd_0_P4V1::getV1ModelVersion
ParseAnnotationBodies_0_ParseAnnotations
ParseAnnotationBodies_1_ClearTypeMap
FrontEnd_1_ParseAnnotationBodies
FrontEnd_2_PrettyPrint
FrontEnd_3_ValidateParsedProgram
FrontEnd_4_CreateBuiltins
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
FrontEnd_11_TypeInference
FrontEnd_12_ValidateMatchAnnotations
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
DefaultArguments_0_TypeChecking
DefaultArguments_1_DoDefaultArguments
FrontEnd_13_DefaultArguments
BindTypeVariables_0_ClearTypeMap
BindTypeVariables_1_ResolveReferences
BindTypeVariables_2_TypeInference
BindTypeVariables_3_DoBindTypeVariables
FrontEnd_14_BindTypeVariables
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
StructInitializers_0_TypeChecking
StructInitializers_1_CreateStructInitializers
StructInitializers_2_ClearTypeMap
FrontEnd_15_StructInitializers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SpecializeGenericFunctions_0_TypeChecking
SpecializeGenericFunctions_1_FindFunctionSpecializations
SpecializeGenericFunctions_2_SpecializeFunctions
FrontEnd_16_SpecializeGenericFunctions
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
TableKeyNames_0_TypeChecking
TableKeyNames_1_DoTableKeyNames
FrontEnd_17_TableKeyNames
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
ConstantFolding_0_TypeChecking
ConstantFolding_1_DoConstantFolding
ConstantFolding_2_ClearTypeMap
PassRepeated_0_ConstantFolding
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
P4::TypeChecking_2_ApplyTypesToExpressions
P4::TypeChecking_3_ResolveReferences
P4::StrengthReduction_0_TypeChecking
P4::StrengthReduction_1_StrengthReduction
PassRepeated_1_StrengthReduction
P4::TypeChecking_0_ResolveReferences
bugs/crash/fixed/2356.p4(36): [--Werror=type-error] error: do_function[-1:0]: negative bit index -1
        tmp = (do_function() << 8w8)[7:0];
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^
*/
#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

struct Meta {
}

bit<16> do_function() {
    return 16w1;
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
        bit<8> tmp;
        tmp = (do_function() << 8w8)[7:0];
    }
}

control vrfy(inout Headers h, inout Meta m) {
    apply {
    }
}

control update(inout Headers h, inout Meta m) {
    apply {
    }
}

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
    }
}

control deparser(packet_out pkt, in Headers h) {
    apply {
        pkt.emit(h);
    }
}

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

