*** dumps/p4_16_samples/union-valid-bmv2.p4/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:54.453252300 +0200
--- dumps/p4_16_samples/union-valid-bmv2.p4/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:54.507942000 +0200
*************** control egress(inout Headers h, inout Me
*** 44,53 ****
  control deparser(packet_out b, in Headers h) {
      apply {
          b.emit<Hdr1>(h.h1);
!         {
!             b.emit<Hdr1>(h.u.h1);
!             b.emit<Hdr2>(h.u.h2);
!         }
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
--- 44,51 ----
  control deparser(packet_out b, in Headers h) {
      apply {
          b.emit<Hdr1>(h.h1);
!         b.emit<Hdr1>(h.u.h1);
!         b.emit<Hdr2>(h.u.h2);
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
*************** control ingress(inout Headers h, inout M
*** 64,73 ****
          default_action = a_0();
      }
      apply {
!         {
!             key_0 = h.u.isValid();
!             t.apply();
!         }
      }
  }
  V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
--- 62,69 ----
          default_action = a_0();
      }
      apply {
!         key_0 = h.u.isValid();
!         t.apply();
      }
  }
  V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
