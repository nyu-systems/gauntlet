*** dumps/p4_16_samples/union3-bmv2.p4/pruned/union3-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:55.737404600 +0200
--- dumps/p4_16_samples/union3-bmv2.p4/pruned/union3-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:55.739671500 +0200
*************** control egress(inout Headers h, inout Me
*** 49,58 ****
  control deparser(packet_out b, in Headers h) {
      apply {
          b.emit<Hdr1>(h.h1);
!         {
!             b.emit<Hdr1>(h.u.h1);
!             b.emit<Hdr2>(h.u.h2);
!         }
          b.emit<Hdr2>(h.h2);
      }
  }
--- 49,56 ----
  control deparser(packet_out b, in Headers h) {
      apply {
          b.emit<Hdr1>(h.h1);
!         b.emit<Hdr1>(h.u.h1);
!         b.emit<Hdr2>(h.u.h2);
          b.emit<Hdr2>(h.h2);
      }
  }
