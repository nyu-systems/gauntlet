*** dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:07.916725800 +0200
--- dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:07.919244100 +0200
*************** control egress(inout Headers h, inout Me
*** 28,34 ****
  }
  control deparser(packet_out b, in Headers h) {
      apply {
!         b.emit<Headers>(h);
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
--- 28,36 ----
  }
  control deparser(packet_out b, in Headers h) {
      apply {
!         {
!             b.emit<hdr>(h.h);
!         }
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
