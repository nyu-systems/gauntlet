*** dumps/p4_16_samples/equality-varbit-bmv2.p4/pruned/equality-varbit-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:58:16.573858500 +0200
--- dumps/p4_16_samples/equality-varbit-bmv2.p4/pruned/equality-varbit-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:58:16.578154700 +0200
*************** control uc(inout headers hdr, inout meta
*** 38,44 ****
  }
  control deparser(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<headers>(hdr);
      }
  }
  V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
--- 38,46 ----
  }
  control deparser(packet_out packet, in headers hdr) {
      apply {
!         {
!             packet.emit<H>(hdr.h);
!         }
      }
  }
  V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
