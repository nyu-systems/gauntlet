*** dumps/p4_16_samples/empty-bmv2.p4/pruned/empty-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:14.356977900 +0200
--- dumps/p4_16_samples/empty-bmv2.p4/pruned/empty-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:14.360915300 +0200
*************** control egress(inout Headers h, inout Me
*** 25,32 ****
  }
  control deparser(packet_out b, in Headers h) {
      apply {
-         {
-         }
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
--- 25,30 ----
