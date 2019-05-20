*** dumps/p4_16_samples/issue561-7-bmv2.p4/pruned/issue561-7-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:35.055977000 +0200
--- dumps/p4_16_samples/issue561-7-bmv2.p4/pruned/issue561-7-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:35.061090100 +0200
*************** control egress(inout headers hdr, inout
*** 66,72 ****
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<headers>(hdr);
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
--- 66,75 ----
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         {
!             packet.emit<S>(hdr.base);
!             packet.emit<U>(hdr.u[0]);
!         }
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
