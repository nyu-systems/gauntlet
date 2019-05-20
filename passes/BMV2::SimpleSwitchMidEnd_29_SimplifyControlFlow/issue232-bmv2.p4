*** dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:02.278603100 +0200
--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:02.334261500 +0200
*************** control Ing(inout Headers headers, inout
*** 22,45 ****
  control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
      Value val_2;
      @name("Eg.test") action test_0() {
!         {
!         }
!         {
!         }
!         {
!         }
!         {
!             {
!                 {
!                     {
!                         val_2.field1 = val_2.field1;
!                     }
!                     val_2.field1 = val_2.field1;
!                     {
!                     }
!                 }
!             }
!         }
      }
      apply {
          test_0();
--- 22,29 ----
  control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
      Value val_2;
      @name("Eg.test") action test_0() {
!         val_2.field1 = val_2.field1;
!         val_2.field1 = val_2.field1;
      }
      apply {
          test_0();
