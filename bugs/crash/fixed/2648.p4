// Invoking preprocessor
// cpp -C -undef -nostdinc -x assembler-with-cpp  -I/storage/Projekte/p4_tv/modules/p4c/build/p4include bugs/crash/index_crash.p4
// FrontEnd_0_P4V1::getV1ModelVersion
// ParseAnnotationBodies_0_ParseAnnotations
// ParseAnnotationBodies_1_ClearTypeMap
// FrontEnd_1_ParseAnnotationBodies
// FrontEnd_2_PrettyPrint
// FrontEnd_3_ValidateParsedProgram
// FrontEnd_4_CreateBuiltins
// FrontEnd_5_ResolveReferences
// ConstantFolding_0_DoConstantFolding
// FrontEnd_6_ConstantFolding
// InstantiateDirectCalls_0_ResolveReferences
// InstantiateDirectCalls_1_DoInstantiateCalls
// FrontEnd_7_InstantiateDirectCalls
// FrontEnd_8_ResolveReferences
// Deprecated_0_ResolveReferences
// Deprecated_1_CheckDeprecated
// FrontEnd_9_Deprecated
// FrontEnd_10_CheckNamedArgs
// FrontEnd_11_TypeInference
// FrontEnd_12_ValidateMatchAnnotations
// BindTypeVariables_0_ClearTypeMap
// BindTypeVariables_1_ResolveReferences
// BindTypeVariables_2_TypeInference
// BindTypeVariables_3_DoBindTypeVariables
// BindTypeVariables_4_ClearTypeMap
// FrontEnd_13_BindTypeVariables
// P4::TypeChecking_0_ResolveReferences
// P4::TypeChecking_1_TypeInference
// PassRepeated_0_TypeChecking
// PassRepeated_1_FindTypeSpecializations
// PassRepeated_2_CreateSpecializedTypes
// PassRepeated_3_ClearTypeMap
// SpecializeGenericTypes_0_PassRepeated
// P4::TypeChecking_0_ResolveReferences
// P4::TypeChecking_1_TypeInference
// SpecializeGenericTypes_1_TypeChecking
// SpecializeGenericTypes_2_ReplaceTypeUses
// SpecializeGenericTypes_3_ClearTypeMap
// FrontEnd_14_SpecializeGenericTypes
// P4::TypeChecking_0_ResolveReferences
// P4::TypeChecking_1_TypeInference
// DefaultArguments_0_TypeChecking
// DefaultArguments_1_DoDefaultArguments
// FrontEnd_15_DefaultArguments
// FrontEnd_16_ResolveReferences
// FrontEnd_17_TypeInference
// RemoveParserControlFlow_0_DoRemoveParserControlFlow
// P4::TypeChecking_0_ResolveReferences
// P4::TypeChecking_1_TypeInference
// SimplifyControlFlow_0_TypeChecking
// SimplifyControlFlow_1_DoSimplifyControlFlow
// RemoveParserControlFlow_1_SimplifyControlFlow
// FrontEnd_18_RemoveParserControlFlow
// P4::TypeChecking_0_ResolveReferences
// P4::TypeChecking_1_TypeInference
// StructInitializers_0_TypeChecking
// terminate called after throwing an instance of 'Util::CompilerBug'
//   what():  In file: /storage/Projekte/p4_tv/modules/p4c/lib/crash.cpp:256
// [31mCompiler Bug[0m: Exiting with SIGSEGV

#include <core.p4>

bit<3> max(in bit<3> val, in bit<3> bound) {
    return 3w2;
}
header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<8> a;
}

struct Headers {
    ethernet_t    eth_hdr;
    H[2]    h;
}

bit<8> give_value(H dummy_hdr) {
    return dummy_hdr.a;
}

parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        transition accept;
    }
}

control ingress(inout Headers h) {
    apply {
        h.h[give_value({8w1})].a = 8w1;
    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

