*** dumps/p4_16_samples/issue1882-bmv2.p4/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:34.265043000 +0200
--- dumps/p4_16_samples/issue1882-bmv2.p4/pruned/issue1882-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:34.267482400 +0200
*************** control egress(inout Headers h, inout Me
*** 25,31 ****
  }
  control deparser(packet_out b, in Headers h) {
      apply {
!         b.emit<Headers>(h);
      }
  }
  extern ExternCounter {
--- 25,32 ----
  }
  control deparser(packet_out b, in Headers h) {
      apply {
!         {
!         }
      }
  }
  extern ExternCounter {
