*** dumps/p4_16_samples/issue210.p4/pruned/issue210-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:01.782255300 +0200
--- dumps/p4_16_samples/issue210.p4/pruned/issue210-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:01.836263900 +0200
***************
*** 2,13 ****
  control Ing(out bit<32> a) {
      bool b;
      @name("Ing.cond") action cond_0() {
!         {
!             {
!                 a = (b ? 32w5 : a);
!                 a = (!b ? 32w10 : a);
!             }
!         }
      }
      apply {
          b = true;
--- 2,9 ----
  control Ing(out bit<32> a) {
      bool b;
      @name("Ing.cond") action cond_0() {
!         a = (b ? 32w5 : a);
!         a = (!b ? 32w10 : a);
      }
      apply {
          b = true;
