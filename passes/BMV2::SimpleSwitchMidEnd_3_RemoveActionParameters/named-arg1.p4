*** dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:48.220973400 +0200
--- dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:48.184918700 +0200
*************** control c(out bool b) {
*** 23,37 ****
      bool b_2;
      bit<16> x_6;
      bool b_3;
!     @name("c.a") action a_0(in bit<16> bi, out bit<16> mb) {
          mb = -bi;
      }
!     @name("c.a") action a_2(in bit<16> bi_1, out bit<16> mb_1) {
          mb_1 = -bi_1;
      }
      apply {
!         a_0(bi = 16w3, mb = xv);
!         a_2(mb = xv, bi = 16w0);
          x_5 = xv;
          b_2 = x_5 == 16w0;
          b = b_2;
--- 23,45 ----
      bool b_2;
      bit<16> x_6;
      bool b_3;
!     bit<16> bi;
!     bit<16> mb;
!     @name("c.a") action a_0() {
!         bi = 16w3;
          mb = -bi;
+         xv = mb;
      }
!     bit<16> bi_1;
!     bit<16> mb_1;
!     @name("c.a") action a_2() {
!         bi_1 = 16w0;
          mb_1 = -bi_1;
+         xv = mb_1;
      }
      apply {
!         a_0();
!         a_2();
          x_5 = xv;
          b_2 = x_5 == 16w0;
          b = b_2;
