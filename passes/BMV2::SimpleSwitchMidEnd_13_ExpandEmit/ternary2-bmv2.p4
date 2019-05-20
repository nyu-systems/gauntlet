*** dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:00:50.171893000 +0200
--- dumps/p4_16_samples/ternary2-bmv2.p4/pruned/ternary2-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 17:00:50.177104700 +0200
*************** control egress(inout packet_t hdrs, inou
*** 162,168 ****
  control deparser(packet_out b, in packet_t hdrs) {
      apply {
          b.emit<data_h>(hdrs.data);
!         b.emit<extra_h[4]>(hdrs.extra);
      }
  }
  V1Switch<packet_t, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
--- 162,173 ----
  control deparser(packet_out b, in packet_t hdrs) {
      apply {
          b.emit<data_h>(hdrs.data);
!         {
!             b.emit<extra_h>(hdrs.extra[0]);
!             b.emit<extra_h>(hdrs.extra[1]);
!             b.emit<extra_h>(hdrs.extra[2]);
!             b.emit<extra_h>(hdrs.extra[3]);
!         }
      }
  }
  V1Switch<packet_t, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
