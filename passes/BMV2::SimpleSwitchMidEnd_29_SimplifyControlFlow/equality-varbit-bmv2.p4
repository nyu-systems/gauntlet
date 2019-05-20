*** dumps/p4_16_samples/equality-varbit-bmv2.p4/pruned/equality-varbit-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:16.674877500 +0200
--- dumps/p4_16_samples/equality-varbit-bmv2.p4/pruned/equality-varbit-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:16.677920700 +0200
*************** control uc(inout headers hdr, inout meta
*** 38,46 ****
  }
  control deparser(packet_out packet, in headers hdr) {
      apply {
!         {
!             packet.emit<H>(hdr.h);
!         }
      }
  }
  V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
--- 38,44 ----
  }
  control deparser(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<H>(hdr.h);
      }
  }
  V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
