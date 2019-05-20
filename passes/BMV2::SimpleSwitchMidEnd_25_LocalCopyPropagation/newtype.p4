*** dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:49.852920800 +0200
--- dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:49.855480800 +0200
*************** header H {
*** 10,19 ****
  }
  control c(out B32 x) {
      N32 k;
-     bit<32> b_1;
-     N32 n_1;
-     N32 n1;
-     S s;
      @name(".NoAction") action NoAction_0() {
      }
      @name("c.t") table t {
--- 10,15 ----
*************** control c(out B32 x) {
*** 26,42 ****
          default_action = NoAction_0();
      }
      apply {
!         b_1 = 32w0;
!         n_1 = b_1;
!         k = n_1;
!         x = (B32)n_1;
!         n1 = 32w1;
!         if (n_1 == n1) 
              x = 32w2;
-         s.b = b_1;
-         s.n = n_1;
          t.apply();
!         if (s.b == (B32)s.n) 
              x = 32w3;
      }
  }
--- 22,33 ----
          default_action = NoAction_0();
      }
      apply {
!         k = 32w0;
!         x = (B32)32w0;
!         if (32w0 == 32w1) 
              x = 32w2;
          t.apply();
!         if (32w0 == (B32)32w0) 
              x = 32w3;
      }
  }
