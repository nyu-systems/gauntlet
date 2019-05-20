*** dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:48.123982700 +0200
--- dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:48.127712900 +0200
*************** control c(out bool b) {
*** 19,31 ****
      bool b_3;
      bit<16> bi;
      bit<16> mb;
      @name("c.a") action a_0() {
          bi = 16w3;
          mb = -bi;
          xv = mb;
      }
-     bit<16> bi_1;
-     bit<16> mb_1;
      @name("c.a") action a_2() {
          bi_1 = 16w0;
          mb_1 = -bi_1;
--- 19,31 ----
      bool b_3;
      bit<16> bi;
      bit<16> mb;
+     bit<16> bi_1;
+     bit<16> mb_1;
      @name("c.a") action a_0() {
          bi = 16w3;
          mb = -bi;
          xv = mb;
      }
      @name("c.a") action a_2() {
          bi_1 = 16w0;
          mb_1 = -bi_1;
