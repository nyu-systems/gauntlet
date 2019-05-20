*** dumps/p4_16_samples/issue561-2-bmv2.p4/pruned/issue561-2-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:18.611841800 +0200
--- dumps/p4_16_samples/issue561-2-bmv2.p4/pruned/issue561-2-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:18.665202500 +0200
*************** control egress(inout headers hdr, inout
*** 69,79 ****
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
--- 69,77 ----
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<S>(hdr.base);
!         packet.emit<O1>(hdr.u.byte);
!         packet.emit<O2>(hdr.u.short);
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
