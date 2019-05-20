*** dumps/p4_16_samples/key1-bmv2.p4/pruned/key1-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:43.715345600 +0200
--- dumps/p4_16_samples/key1-bmv2.p4/pruned/key1-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:43.717722700 +0200
*************** control deparser(packet_out b, in Header
*** 33,44 ****
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      @name(".NoAction") action NoAction_0() {
      }
      @name("ingress.c.a") action c_a() {
          h.h.b = h.h.a;
      }
-     bit<32> key_0;
      @name("ingress.c.t") table c_t_0 {
          key = {
              key_0: exact @name("e") ;
--- 33,44 ----
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
+     bit<32> key_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("ingress.c.a") action c_a() {
          h.h.b = h.h.a;
      }
      @name("ingress.c.t") table c_t_0 {
          key = {
              key_0: exact @name("e") ;
