*** dumps/p4_16_samples/subparser-with-header-stack-bmv2.p4/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:00:37.165654100 +0200
--- dumps/p4_16_samples/subparser-with-header-stack-bmv2.p4/pruned/subparser-with-header-stack-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:00:37.170772600 +0200
*************** control uc(inout headers hdr, inout meta
*** 105,111 ****
  control DeparserI(packet_out packet, in headers hdr) {
      apply {
          packet.emit<h1_t>(hdr.h1);
!         packet.emit<h2_t[5]>(hdr.h2);
          packet.emit<h3_t>(hdr.h3);
      }
  }
--- 105,117 ----
  control DeparserI(packet_out packet, in headers hdr) {
      apply {
          packet.emit<h1_t>(hdr.h1);
!         {
!             packet.emit<h2_t>(hdr.h2[0]);
!             packet.emit<h2_t>(hdr.h2[1]);
!             packet.emit<h2_t>(hdr.h2[2]);
!             packet.emit<h2_t>(hdr.h2[3]);
!             packet.emit<h2_t>(hdr.h2[4]);
!         }
          packet.emit<h3_t>(hdr.h3);
      }
  }
