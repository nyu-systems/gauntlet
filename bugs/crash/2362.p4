/*Invoking preprocessor
cpp -C -undef -nostdinc -x assembler-with-cpp  -Ip4_tv/p4c/build/p4include -D__TARGET_BMV2__ -Ip4_tv/p4c/build/p4include -Ip4_tv/p4c/build/p4include ./2362.p4i
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
FrontEnd_16_ConstantFolding
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
P4::TypeChecking_2_ApplyTypesToExpressions
P4::TypeChecking_3_ResolveReferences
P4::StrengthReduction_0_TypeChecking
P4::StrengthReduction_1_StrengthReduction
FrontEnd_17_StrengthReduction
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
UselessCasts_0_TypeChecking
UselessCasts_1_RemoveUselessCasts
FrontEnd_18_UselessCasts
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
FrontEnd_19_SimplifyControlFlow
FrontEnd_20_FrontEndDump
PassRepeated_0_ResolveReferences
PassRepeated_1_RemoveUnusedDeclarations
PassRepeated_2_ResolveReferences
PassRepeated_3_RemoveUnusedDeclarations
PassRepeated_4_ResolveReferences
PassRepeated_5_RemoveUnusedDeclarations
RemoveAllUnusedDeclarations_0_PassRepeated
FrontEnd_21_RemoveAllUnusedDeclarations
SimplifyParsers_0_ResolveReferences
SimplifyParsers_1_DoSimplifyParsers
FrontEnd_22_SimplifyParsers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
ResetHeaders_0_TypeChecking
ResetHeaders_1_DoResetHeaders
FrontEnd_23_ResetHeaders
UniqueNames_0_ResolveReferences
UniqueNames_1_FindSymbols
UniqueNames_2_RenameSymbols
FrontEnd_24_UniqueNames
FrontEnd_25_MoveDeclarations
FrontEnd_26_MoveInitializers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SideEffectOrdering_0_TypeChecking
SideEffectOrdering_1_DoSimplifyExpressions
FrontEnd_27_SideEffectOrdering
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SetHeaders_0_TypeChecking
SetHeaders_1_DoSetHeaders
FrontEnd_28_SetHeaders
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
P4::TypeChecking_2_ResolveReferences
P4::TypeChecking_3_TypeInference
SimplifyControlFlow_2_TypeChecking
SimplifyControlFlow_3_DoSimplifyControlFlow
FrontEnd_29_SimplifyControlFlow
FrontEnd_30_MoveDeclarations
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyDefUse_0_TypeChecking
In file: p4_tv/p4c/frontends/p4/def_use.h:347
[31mCompiler Bug[0m: h.eth_hdr.eth_type: no definitions

running cc -E -C -undef -nostdinc -x assembler-with-cpp -I p4_tv/p4c/build/p4include -o ./2362.p4i bugs/crash/2362.p4
running p4_tv/p4c/build/p4c-bm2-ss -I p4_tv/p4c/build/p4include --p4v=16 -vvv -o ./2362.json ./2362.p4i --arch v1model
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

bit<16> simple_action() {
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

    table sub_table {
        key = {
            h.eth_hdr.eth_type: exact @name("dummy_name") ;
        }
        actions = {
        }
    }

    table simple_table {
        key = {
            sub_table.apply().hit: exact @name("dummy_name") ;
        }
        actions = {
        }
    }
    apply {
        simple_table.apply();
    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {b.emit(h);} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

