*** dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:48.132022700 +0200
--- dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:48.135903700 +0200
*************** parser par(out bool b) {
*** 13,56 ****
  }
  control c(out bool b) {
      bit<16> xv;
-     bit<16> x_5;
-     bool b_2;
-     bit<16> x_6;
      bool b_3;
-     bit<16> bi;
-     bit<16> mb;
-     bit<16> bi_1;
-     bit<16> mb_1;
      @name("c.a") action a_0() {
!         bi = 16w3;
!         mb = -bi;
!         xv = mb;
      }
      @name("c.a") action a_2() {
!         bi_1 = 16w0;
!         mb_1 = -bi_1;
!         xv = mb_1;
      }
      apply {
          a_0();
          a_2();
!         x_5 = xv;
!         b_2 = x_5 == 16w0;
!         b = b_2;
!         xv = x_5;
!         x_6 = xv;
!         b_3 = x_6 == 16w1;
!         xv = x_6;
          b = b_3;
          xv = 16w1;
!         x_5 = xv;
!         b_2 = x_5 == 16w0;
!         xv = x_5;
!         b = b_2;
!         x_6 = xv;
!         b_3 = x_6 == 16w1;
!         b = b_3;
!         xv = x_6;
      }
  }
  control ce(out bool b);
--- 13,37 ----
  }
  control c(out bool b) {
      bit<16> xv;
      bool b_3;
      @name("c.a") action a_0() {
!         xv = -16w3;
      }
      @name("c.a") action a_2() {
!         xv = -16w0;
      }
      apply {
          a_0();
          a_2();
!         b = xv == 16w0;
!         b_3 = xv == 16w1;
          b = b_3;
          xv = 16w1;
!         xv = 16w1;
!         b = 16w1 == 16w0;
!         b_3 = 16w1 == 16w1;
!         b = 16w1 == 16w1;
!         xv = 16w1;
      }
  }
  control ce(out bool b);
