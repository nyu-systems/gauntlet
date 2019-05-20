*** dumps/p4_16_samples/issue774-4-bmv2.p4/pruned/issue774-4-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:26.803737700 +0200
--- dumps/p4_16_samples/issue774-4-bmv2.p4/pruned/issue774-4-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:26.806752100 +0200
*************** control cc(inout Headers hdr, inout M me
*** 34,40 ****
  }
  control d(packet_out b, in Headers hdr) {
      apply {
!         b.emit<Headers>(hdr);
      }
  }
  V1Switch<Headers, M>(prs(), vc(), i(), e(), cc(), d()) main;
--- 34,42 ----
  }
  control d(packet_out b, in Headers hdr) {
      apply {
!         {
!             b.emit<Header>(hdr.h);
!         }
      }
  }
  V1Switch<Headers, M>(prs(), vc(), i(), e(), cc(), d()) main;
