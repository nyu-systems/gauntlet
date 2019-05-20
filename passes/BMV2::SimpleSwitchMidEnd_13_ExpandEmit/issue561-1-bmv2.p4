*** dumps/p4_16_samples/issue561-1-bmv2.p4/pruned/issue561-1-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:18.106654400 +0200
--- dumps/p4_16_samples/issue561-1-bmv2.p4/pruned/issue561-1-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:18.109184200 +0200
*************** control egress(inout headers hdr, inout
*** 66,72 ****
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<headers>(hdr);
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
--- 66,76 ----
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         {
!             packet.emit<S>(hdr.base);
!             packet.emit<O1>(hdr.u.byte);
!             packet.emit<O2>(hdr.u.short);
!         }
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
