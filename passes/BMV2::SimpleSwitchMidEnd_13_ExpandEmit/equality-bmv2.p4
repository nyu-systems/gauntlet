*** dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:58:16.150075100 +0200
--- dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:58:16.153348600 +0200
*************** control uc(inout headers hdr, inout meta
*** 54,60 ****
  }
  control deparser(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<headers>(hdr);
      }
  }
  V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
--- 54,65 ----
  }
  control deparser(packet_out packet, in headers hdr) {
      apply {
!         {
!             packet.emit<H>(hdr.h);
!             packet.emit<H>(hdr.a[0]);
!             packet.emit<H>(hdr.a[1]);
!             packet.emit<Same>(hdr.same);
!         }
      }
  }
  V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
