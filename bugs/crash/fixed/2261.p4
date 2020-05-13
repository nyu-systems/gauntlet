/*Invoking preprocessor
cpp -C -undef -nostdinc -x assembler-with-cpp  -D__TARGET_BMV2__ -Ip4_tv/p4c/build/backends/bmv2/p4include bugs/crash/fixed/2261.p4
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
FrontEnd_10_TypeInference
FrontEnd_11_ValidateMatchAnnotations
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
DefaultArguments_0_TypeChecking
DefaultArguments_1_DoDefaultArguments
FrontEnd_12_DefaultArguments
BindTypeVariables_0_ClearTypeMap
BindTypeVariables_1_ResolveReferences
BindTypeVariables_2_TypeInference
BindTypeVariables_3_DoBindTypeVariables
FrontEnd_13_BindTypeVariables
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
StructInitializers_0_TypeChecking
StructInitializers_1_CreateStructInitializers
StructInitializers_2_ClearTypeMap
FrontEnd_14_StructInitializers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
TableKeyNames_0_TypeChecking
TableKeyNames_1_DoTableKeyNames
FrontEnd_15_TableKeyNames
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
P4::TypeChecking_1_TypeInference
UselessCasts_0_TypeChecking
UselessCasts_1_RemoveUselessCasts
PassRepeated_2_UselessCasts
P4::TypeChecking_2_ResolveReferences
P4::TypeChecking_3_TypeInference
ConstantFolding_3_TypeChecking
ConstantFolding_4_DoConstantFolding
ConstantFolding_5_ClearTypeMap
PassRepeated_3_ConstantFolding
P4::TypeChecking_4_ResolveReferences
P4::TypeChecking_5_TypeInference
P4::TypeChecking_6_ApplyTypesToExpressions
P4::TypeChecking_7_ResolveReferences
P4::StrengthReduction_2_TypeChecking
P4::StrengthReduction_3_StrengthReduction
PassRepeated_4_StrengthReduction
P4::TypeChecking_2_ResolveReferences
P4::TypeChecking_3_TypeInference
UselessCasts_2_TypeChecking
UselessCasts_3_RemoveUselessCasts
PassRepeated_5_UselessCasts
FrontEnd_16_PassRepeated
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
FrontEnd_17_SimplifyControlFlow
FrontEnd_18_SwitchAddDefault
FrontEnd_19_FrontEndDump
PassRepeated_0_ResolveReferences
PassRepeated_1_RemoveUnusedDeclarations
PassRepeated_2_ResolveReferences
PassRepeated_3_RemoveUnusedDeclarations
PassRepeated_4_ResolveReferences
PassRepeated_5_RemoveUnusedDeclarations
RemoveAllUnusedDeclarations_0_PassRepeated
FrontEnd_20_RemoveAllUnusedDeclarations
SimplifyParsers_0_ResolveReferences
SimplifyParsers_1_DoSimplifyParsers
FrontEnd_21_SimplifyParsers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
ResetHeaders_0_TypeChecking
ResetHeaders_1_DoResetHeaders
FrontEnd_22_ResetHeaders
UniqueNames_0_ResolveReferences
UniqueNames_1_FindSymbols
UniqueNames_2_RenameSymbols
FrontEnd_23_UniqueNames
FrontEnd_24_MoveDeclarations
FrontEnd_25_MoveInitializers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SideEffectOrdering_0_TypeChecking
SideEffectOrdering_1_DoSimplifyExpressions
FrontEnd_26_SideEffectOrdering
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SetHeaders_0_TypeChecking
SetHeaders_1_DoSetHeaders
FrontEnd_27_SetHeaders
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
P4::TypeChecking_2_ResolveReferences
P4::TypeChecking_3_TypeInference
SimplifyControlFlow_2_TypeChecking
SimplifyControlFlow_3_DoSimplifyControlFlow
FrontEnd_28_SimplifyControlFlow
FrontEnd_29_MoveDeclarations
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyDefUse_0_TypeChecking
bugs/crash/fixed/2261.p4(22): [--Werror=duplicate] error: eth_hdr: Duplicates declaration eth_hdr
    nested_struct tmp_struct = { { 0, 0, 0 } };
                                 ^^^^^^^^^^^
bugs/crash/fixed/2261.p4(11)
    ethernet_t eth_hdr;
               ^^^^^^^
bugs/crash/fixed/2261.p4(22): [--Werror=duplicate] error: dst_addr: Duplicates declaration dst_addr
    nested_struct tmp_struct = { { 0, 0, 0 } };
                                   ^
bugs/crash/fixed/2261.p4(5)
    bit<48> dst_addr;
            ^^^^^^^^
bugs/crash/fixed/2261.p4(22): [--Werror=duplicate] error: src_addr: Duplicates declaration src_addr
    nested_struct tmp_struct = { { 0, 0, 0 } };
                                      ^
bugs/crash/fixed/2261.p4(6)
    bit<48> src_addr;
            ^^^^^^^^
bugs/crash/fixed/2261.p4(22): [--Werror=duplicate] error: eth_type: Duplicates declaration eth_type
    nested_struct tmp_struct = { { 0, 0, 0 } };
                                         ^
bugs/crash/fixed/2261.p4(7)
    bit<16> eth_type;
            ^^^^^^^^
*/

#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct nested_struct {
    ethernet_t     eth_hdr;
}

struct Headers {
    ethernet_t eth_hdr;
}

struct Meta {
}

bit<16> simple_function() {
    nested_struct tmp_struct = { { 0, 0, 0 } };
    return tmp_struct.eth_hdr.eth_type;
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
        h.eth_hdr.eth_type = simple_function();
    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {b.emit(h);} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

