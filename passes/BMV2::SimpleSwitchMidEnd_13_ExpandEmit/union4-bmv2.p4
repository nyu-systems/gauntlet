*** dumps/p4_16_samples/union4-bmv2.p4/pruned/union4-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:00:56.114917700 +0200
--- dumps/p4_16_samples/union4-bmv2.p4/pruned/union4-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:00:56.116964800 +0200
*************** control egress(inout Headers h, inout Me
*** 49,55 ****
  control deparser(packet_out b, in Headers h) {
      apply {
          b.emit<Hdr1>(h.h1);
!         b.emit<U>(h.u);
          b.emit<Hdr2>(h.h2);
      }
  }
--- 49,58 ----
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
