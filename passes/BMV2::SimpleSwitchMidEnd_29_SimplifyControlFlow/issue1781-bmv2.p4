*** dumps/p4_16_samples/issue1781-bmv2.p4/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:57.412571000 +0200
--- dumps/p4_16_samples/issue1781-bmv2.p4/pruned/issue1781-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:57.473220400 +0200
*************** bit<32> test_func() {
*** 14,21 ****
  }
  control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
      @name("IngressImpl.update_value") action update_value_0() {
-         {
-         }
      }
      apply {
          test_func();
--- 14,19 ----
