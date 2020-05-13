/*Invoking preprocessor
cpp -C -undef -nostdinc -x assembler-with-cpp  -Ip4_tv/p4c/build/p4include -D__TARGET_BMV2__ -Ip4_tv/p4c/build/p4include -Ip4_tv/p4c/build/backends/bmv2/p4include ./parser_loop.p4i
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
FrontEnd_18_PassRepeated
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
FrontEnd_19_SimplifyControlFlow
FrontEnd_20_SwitchAddDefault
FrontEnd_21_FrontEndDump
PassRepeated_0_ResolveReferences
PassRepeated_1_RemoveUnusedDeclarations
PassRepeated_2_ResolveReferences
PassRepeated_3_RemoveUnusedDeclarations
PassRepeated_4_ResolveReferences
PassRepeated_5_RemoveUnusedDeclarations
RemoveAllUnusedDeclarations_0_PassRepeated
FrontEnd_22_RemoveAllUnusedDeclarations
SimplifyParsers_0_ResolveReferences
bugs/crash/parser_loop.p4(27): [--Wwarn=parser-transition] warning: accept state in parser PROTParser is unreachable
parser PROTParser(packet_in packet,
       ^^^^^^^^^^
SimplifyParsers_1_DoSimplifyParsers
FrontEnd_23_SimplifyParsers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
ResetHeaders_0_TypeChecking
ResetHeaders_1_DoResetHeaders
FrontEnd_24_ResetHeaders
UniqueNames_0_ResolveReferences
UniqueNames_1_FindSymbols
UniqueNames_2_RenameSymbols
FrontEnd_25_UniqueNames
FrontEnd_26_MoveDeclarations
FrontEnd_27_MoveInitializers
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SideEffectOrdering_0_TypeChecking
SideEffectOrdering_1_DoSimplifyExpressions
FrontEnd_28_SideEffectOrdering
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SetHeaders_0_TypeChecking
SetHeaders_1_DoSetHeaders
FrontEnd_29_SetHeaders
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyControlFlow_0_TypeChecking
SimplifyControlFlow_1_DoSimplifyControlFlow
FrontEnd_30_SimplifyControlFlow
FrontEnd_31_MoveDeclarations
P4::TypeChecking_0_ResolveReferences
P4::TypeChecking_1_TypeInference
SimplifyDefUse_0_TypeChecking
In file: p4_tv/p4c/frontends/p4/def_use.h:351
[31mCompiler Bug[0m: no definitions found for hdr.h.h

running cc -E -C -undef -nostdinc -x assembler-with-cpp -I p4_tv/p4c/build/p4include -o ./parser_loop.p4i bugs/crash/parser_loop.p4
running p4_tv/p4c/build/p4c-bm2-ss -I p4_tv/p4c/build/p4include --p4v=16 -vvv -o ./parser_loop.json ./parser_loop.p4i --arch v1model
*/

#include <core.p4>
#include <v1model.p4>


/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

header H {
    bit<8>  h;
}

struct metadata {
}

struct headers {
    H h;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/



parser PROTParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        transition state_1;
    }
    state state_1 {
        transition state_2;
    }
    state state_2 {
        transition state_3;
    }
    state state_3 {
        transition state_2;
    }

}


/*************************************************************************
************   C H E C K S U M    V E R I F I C A T I O N   *************
*************************************************************************/

control PROTVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}


/*************************************************************************
**************  I N G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control PROTIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
    }
}

/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control PROTEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
   apply {
    }
}

/*************************************************************************
*************   C H E C K S U M    C O M P U T A T I O N   **************
*************************************************************************/

control PROTComputeChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}


/*************************************************************************
***********************  D E P A R S E R  *******************************
*************************************************************************/

control PROTDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr);
    }
}

/*************************************************************************
***********************  S W I T C H  *******************************
*************************************************************************/

V1Switch(
PROTParser(),
PROTVerifyChecksum(),
PROTIngress(),
PROTEgress(),
PROTComputeChecksum(),
PROTDeparser()
) main;
