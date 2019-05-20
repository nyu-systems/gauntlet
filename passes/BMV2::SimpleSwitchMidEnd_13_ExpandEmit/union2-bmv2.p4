*** dumps/p4_16_samples/union2-bmv2.p4/pruned/union2-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:00:55.251601400 +0200
--- dumps/p4_16_samples/union2-bmv2.p4/pruned/union2-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:00:55.254382300 +0200
*************** control egress(inout Headers h, inout Me
*** 48,54 ****
  control deparser(packet_out b, in Headers h) {
      apply {
          b.emit<Hdr1>(h.h1);
!         b.emit<U>(h.u);
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
--- 48,57 ----
  control deparser(packet_out b, in Headers h) {
      apply {
          b.emit<Hdr1>(h.h1);
!         {
!             b.emit<Hdr1>(h.u.h1);
!             b.emit<Hdr2>(h.u.h2);
!         }
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
