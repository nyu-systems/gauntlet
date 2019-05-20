*** dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:16.198970400 +0200
--- dumps/p4_16_samples/equality-bmv2.p4/pruned/equality-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:16.254152500 +0200
*************** control uc(inout headers hdr, inout meta
*** 54,65 ****
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
--- 54,63 ----
  }
  control deparser(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<H>(hdr.h);
!         packet.emit<H>(hdr.a[0]);
!         packet.emit<H>(hdr.a[1]);
!         packet.emit<Same>(hdr.same);
      }
  }
  V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;
