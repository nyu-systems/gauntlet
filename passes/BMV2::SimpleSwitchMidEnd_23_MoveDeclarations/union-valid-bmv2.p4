*** dumps/p4_16_samples/union-valid-bmv2.p4/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 17:00:54.434663300 +0200
--- dumps/p4_16_samples/union-valid-bmv2.p4/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 17:00:54.436916500 +0200
*************** control deparser(packet_out b, in Header
*** 51,59 ****
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      @name("ingress.a") action a_0() {
      }
-     bool key_0;
      @name("ingress.t") table t {
          key = {
              key_0: exact @name("h.u.$valid$") ;
--- 51,59 ----
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
+     bool key_0;
      @name("ingress.a") action a_0() {
      }
      @name("ingress.t") table t {
          key = {
              key_0: exact @name("h.u.$valid$") ;
