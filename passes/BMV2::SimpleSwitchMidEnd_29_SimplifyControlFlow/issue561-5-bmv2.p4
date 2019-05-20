*** dumps/p4_16_samples/issue561-5-bmv2.p4/pruned/issue561-5-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:20.254810300 +0200
--- dumps/p4_16_samples/issue561-5-bmv2.p4/pruned/issue561-5-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:20.305973900 +0200
*************** control egress(inout headers hdr, inout
*** 65,74 ****
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
--- 65,72 ----
  }
  control DeparserImpl(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<S>(hdr.base);
!         packet.emit<U>(hdr.u[0]);
      }
  }
  control verifyChecksum(inout headers hdr, inout metadata meta) {
