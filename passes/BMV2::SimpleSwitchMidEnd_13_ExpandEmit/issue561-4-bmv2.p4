*** dumps/p4_16_samples/issue561-4-bmv2.p4/pruned/issue561-4-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:19.672615100 +0200
--- dumps/p4_16_samples/issue561-4-bmv2.p4/pruned/issue561-4-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:19.675400800 +0200
*************** control egress(inout headers hdr, inout
*** 85,91 ****
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<headers>(hdr);
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
--- 85,95 ----
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         {
!             packet.emit<S>(hdr.base);
!             packet.emit<U>(hdr.u[0]);
!             packet.emit<U>(hdr.u[1]);
!         }
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
