*** dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:07.948700300 +0200
--- dumps/p4_16_samples/issue323.p4/pruned/issue323-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:07.950891700 +0200
*************** control deparser(packet_out b, in Header
*** 35,45 ****
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      bit<32> v;
      @name("ingress.my_a") action my_a_0() {
          v = 32w0;
          h.h.f = v;
      }
-     bit<32> v_1;
      @name("ingress.my_a") action my_a_2() {
          v_1 = 32w1;
          h.h.f = v_1;
--- 35,45 ----
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      bit<32> v;
+     bit<32> v_1;
      @name("ingress.my_a") action my_a_0() {
          v = 32w0;
          h.h.f = v;
      }
      @name("ingress.my_a") action my_a_2() {
          v_1 = 32w1;
          h.h.f = v_1;
