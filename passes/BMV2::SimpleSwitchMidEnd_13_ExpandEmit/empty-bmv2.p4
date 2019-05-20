*** dumps/p4_16_samples/empty-bmv2.p4/pruned/empty-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:58:14.317108200 +0200
--- dumps/p4_16_samples/empty-bmv2.p4/pruned/empty-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:58:14.319188000 +0200
*************** control egress(inout Headers h, inout Me
*** 25,31 ****
  }
  control deparser(packet_out b, in Headers h) {
      apply {
!         b.emit<Headers>(h);
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
--- 25,32 ----
  }
  control deparser(packet_out b, in Headers h) {
      apply {
!         {
!         }
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
