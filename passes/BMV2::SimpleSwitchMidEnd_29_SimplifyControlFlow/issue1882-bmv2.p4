*** dumps/p4_16_samples/issue1882-bmv2.p4/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:34.319067200 +0200
--- dumps/p4_16_samples/issue1882-bmv2.p4/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:34.386415200 +0200
*************** control egress(inout Headers h, inout Me
*** 25,32 ****
  }
  control deparser(packet_out b, in Headers h) {
      apply {
-         {
-         }
      }
  }
  extern ExternCounter {
--- 25,30 ----
