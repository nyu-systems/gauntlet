*** dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:34.686725500 +0200
--- dumps/p4_16_samples/inline-stack-bmv2.p4/pruned/inline-stack-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:34.692013100 +0200
*************** control ComputeChecksumI(inout H hdr, in
*** 24,37 ****
  }
  control IngressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
      apply {
-         {
-         }
-         {
-         }
-         {
-         }
-         {
-         }
      }
  }
  control EgressI(inout H hdr, inout M meta, inout std_meta_t std_meta) {
--- 24,29 ----
