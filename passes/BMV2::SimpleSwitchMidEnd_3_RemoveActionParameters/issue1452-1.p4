*** dumps/p4_16_samples/issue1452-1.p4/pruned/issue1452-1-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:45.705354100 +0200
--- dumps/p4_16_samples/issue1452-1.p4/pruned/issue1452-1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:45.680683200 +0200
***************
*** 1,10 ****
  control c() {
      bit<32> x;
!     @name("c.b") action b_0(out bit<32> arg) {
          arg = 32w2;
      }
      apply {
!         b_0(x);
      }
  }
  control proto();
--- 1,12 ----
  control c() {
      bit<32> x;
!     bit<32> arg;
!     @name("c.b") action b_0() {
          arg = 32w2;
+         x = arg;
      }
      apply {
!         b_0();
      }
  }
  control proto();
