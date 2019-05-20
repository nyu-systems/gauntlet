*** dumps/p4_16_samples/issue933.p4/pruned/issue933-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:37.186671100 +0200
--- dumps/p4_16_samples/issue933.p4/pruned/issue933-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:37.190202900 +0200
*************** struct headers {
*** 5,11 ****
  }
  control MyDeparser(packet_out packet, in headers hdr) {
      apply {
!         packet.emit<headers>({  });
      }
  }
  Switch<headers>(MyDeparser()) main;
--- 5,12 ----
  }
  control MyDeparser(packet_out packet, in headers hdr) {
      apply {
!         {
!         }
      }
  }
  Switch<headers>(MyDeparser()) main;
