*** dumps/p4_16_samples/stack_complex-bmv2.p4/pruned/stack_complex-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:30.803339200 +0200
--- dumps/p4_16_samples/stack_complex-bmv2.p4/pruned/stack_complex-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:30.805857300 +0200
*************** control egress(inout Headers h, inout Me
*** 35,45 ****
  }
  control deparser(packet_out b, in Headers h) {
      apply {
!         {
!             b.emit<hdr>(h.hs[0]);
!             b.emit<hdr>(h.hs[1]);
!             b.emit<hdr>(h.hs[2]);
!         }
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
--- 35,43 ----
  }
  control deparser(packet_out b, in Headers h) {
      apply {
!         b.emit<hdr>(h.hs[0]);
!         b.emit<hdr>(h.hs[1]);
!         b.emit<hdr>(h.hs[2]);
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
