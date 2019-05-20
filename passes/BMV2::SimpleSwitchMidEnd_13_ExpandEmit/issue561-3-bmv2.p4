*** dumps/p4_16_samples/issue561-3-bmv2.p4/pruned/issue561-3-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:19.146042000 +0200
--- dumps/p4_16_samples/issue561-3-bmv2.p4/pruned/issue561-3-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:19.148488600 +0200
*************** control egress(inout headers hdr, inout
*** 75,81 ****
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<headers>(hdr);
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
--- 75,85 ----
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
