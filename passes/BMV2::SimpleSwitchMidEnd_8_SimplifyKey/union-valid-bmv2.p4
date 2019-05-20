*** dumps/p4_16_samples/union-valid-bmv2.p4/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_7_TypeChecking.p4	2019-05-20 17:00:54.491838300 +0200
--- dumps/p4_16_samples/union-valid-bmv2.p4/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-05-20 17:00:54.494365600 +0200
*************** control deparser(packet_out b, in Header
*** 50,58 ****
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      @name("ingress.a") action a_0() {
      }
      @name("ingress.t") table t {
          key = {
!             h.u.isValid(): exact @name("h.u.$valid$") ;
          }
          actions = {
              a_0();
--- 50,59 ----
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      @name("ingress.a") action a_0() {
      }
+     bool key_0;
      @name("ingress.t") table t {
          key = {
!             key_0: exact @name("h.u.$valid$") ;
          }
          actions = {
              a_0();
*************** control ingress(inout Headers h, inout M
*** 60,66 ****
          default_action = a_0();
      }
      apply {
!         t.apply();
      }
  }
  V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
--- 61,70 ----
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
