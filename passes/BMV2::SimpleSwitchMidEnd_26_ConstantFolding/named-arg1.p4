*** dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:48.135903700 +0200
--- dumps/p4_16_samples/named-arg1.p4/pruned/named-arg1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:59:48.141040500 +0200
*************** control c(out bool b) {
*** 15,24 ****
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
--- 15,24 ----
      bit<16> xv;
      bool b_3;
      @name("c.a") action a_0() {
!         xv = 16w65533;
      }
      @name("c.a") action a_2() {
!         xv = 16w0;
      }
      apply {
          a_0();
*************** control c(out bool b) {
*** 28,36 ****
          b = b_3;
          xv = 16w1;
          xv = 16w1;
!         b = 16w1 == 16w0;
!         b_3 = 16w1 == 16w1;
!         b = 16w1 == 16w1;
          xv = 16w1;
      }
  }
--- 28,36 ----
          b = b_3;
          xv = 16w1;
          xv = 16w1;
!         b = false;
!         b_3 = true;
!         b = true;
          xv = 16w1;
      }
  }
