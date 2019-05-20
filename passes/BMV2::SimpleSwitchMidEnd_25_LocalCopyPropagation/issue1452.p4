*** dumps/p4_16_samples/issue1452.p4/pruned/issue1452-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:45.915898500 +0200
--- dumps/p4_16_samples/issue1452.p4/pruned/issue1452-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:45.919274900 +0200
***************
*** 1,13 ****
  control c() {
      bit<32> x;
-     bool hasReturned_0;
-     bit<32> arg;
      @name("c.a") action a_0() {
!         arg = x;
!         hasReturned_0 = false;
!         arg = 32w1;
!         hasReturned_0 = true;
!         x = arg;
      }
      apply {
          a_0();
--- 1,7 ----
  control c() {
      bit<32> x;
      @name("c.a") action a_0() {
!         x = 32w1;
      }
      apply {
          a_0();
