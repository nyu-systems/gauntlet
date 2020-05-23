/*Invoking preprocessor
cpp -C -undef -nostdinc -x assembler-with-cpp  -Ip4_tv/p4c/build/p4include -D__TARGET_BMV2__ -Ip4_tv/p4c/build/p4include -Ip4_tv/p4c/build/p4include ./bools_and_globals.p4i
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
RemoveParserControlFlow_0_DoRemoveParserControlFlow
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
RemoveParserControlFlow_1_SimplifyControlFlow
FrontEnd_15_RemoveParserControlFlow
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
StructInitializers_0_TypeChecking
StructInitializers_1_CreateStructInitializers
StructInitializers_2_ClearTypeMap
FrontEnd_16_StructInitializers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SpecializeGenericFunctions_0_TypeChecking
SpecializeGenericFunctions_1_FindFunctionSpecializations
SpecializeGenericFunctions_2_SpecializeFunctions
FrontEnd_17_SpecializeGenericFunctions
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
TableKeyNames_0_TypeChecking
TableKeyNames_1_DoTableKeyNames
FrontEnd_18_TableKeyNames
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
FrontEnd_19_PassRepeated
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
FrontEnd_20_SimplifyControlFlow
FrontEnd_21_SwitchAddDefault
FrontEnd_22_FrontEndDump
PassRepeated_0_ResolveReferences
PassRepeated_1_RemoveUnusedDeclarations
PassRepeated_2_ResolveReferences
PassRepeated_3_RemoveUnusedDeclarations
PassRepeated_4_ResolveReferences
PassRepeated_5_RemoveUnusedDeclarations
RemoveAllUnusedDeclarations_0_PassRepeated
FrontEnd_23_RemoveAllUnusedDeclarations
SimplifyParsers_0_ResolveReferences
SimplifyParsers_1_DoSimplifyParsers
FrontEnd_24_SimplifyParsers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
ResetHeaders_0_TypeChecking
ResetHeaders_1_DoResetHeaders
FrontEnd_25_ResetHeaders
UniqueNames_0_ResolveReferences
UniqueNames_1_FindSymbols
UniqueNames_2_RenameSymbols
FrontEnd_26_UniqueNames
FrontEnd_27_MoveDeclarations
FrontEnd_28_MoveInitializers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SideEffectOrdering_0_TypeChecking
SideEffectOrdering_1_DoSimplifyExpressions
FrontEnd_29_SideEffectOrdering
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SetHeaders_0_TypeChecking
SetHeaders_1_DoSetHeaders
FrontEnd_30_SetHeaders
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
P4::TypeChecking_2_ResolveReferences
P4::TypeChecking_3_TypeInference
SimplifyControlFlow_2_TypeChecking
SimplifyControlFlow_3_DoSimplifyControlFlow
FrontEnd_31_SimplifyControlFlow
FrontEnd_32_MoveDeclarations
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyDefUse_0_TypeChecking
bugs/crash/bools_and_globals.p4(19): [--Wwarn=uninitialized_use] warning: tmp may be uninitialized
    tmp = tmp * (make_zero ? 16w0: 16w1);
          ^^^
bugs/crash/bools_and_globals.p4(17): [--Wwarn=uninitialized_out_param] warning: out parameter val_undefined may be uninitialized when do_global_action terminates
action do_global_action(in bool make_zero, out bool val_undefined) {
                                                    ^^^^^^^^^^^^^
bugs/crash/bools_and_globals.p4(17)
action do_global_action(in bool make_zero, out bool val_undefined) {
       ^^^^^^^^^^^^^^^^
In file: p4_tv/p4c/frontends/p4/def_use.h:351
[31mCompiler Bug[0m: no definitions found for tmp

running cc -E -C -undef -nostdinc -x assembler-with-cpp -I p4_tv/p4c/build/p4include -o ./bools_and_globals.p4i bugs/crash/bools_and_globals.p4
running p4_tv/p4c/build/p4c-bm2-ss -I p4_tv/p4c/build/p4include --p4v=16 -vvv -o ./bools_and_globals.json ./bools_and_globals.p4i --arch v1model*/


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

action do_global_action(in bool make_zero, out bool val_undefined) {
    bit<16> tmp;
    tmp = tmp *  (make_zero ? 16w0: 16w1);
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
    bool filler_bool = true;
    bool tmp_bool = false;
    action do_action() {
        do_global_action(tmp_bool, tmp_bool);
    }

    table simple_table {
        key = {
            h.eth_hdr.src_addr : exact;
        }
        actions = {
            do_action();
            do_global_action(true, filler_bool);
        }
    }
    apply {
        simple_table.apply();
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

