*** dumps/p4_16_samples/issue210.p4/pruned/issue210-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:01.769433800 +0200
--- dumps/p4_16_samples/issue210.p4/pruned/issue210-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:01.772881300 +0200
***************
*** 1,17 ****
  #include <core.p4>
  control Ing(out bit<32> a) {
      bool b;
-     bool cond;
-     bool pred;
      @name("Ing.cond") action cond_0() {
          {
              {
!                 cond = b;
!                 pred = cond;
!                 a = (pred ? 32w5 : a);
!                 cond = !cond;
!                 pred = cond;
!                 a = (pred ? 32w10 : a);
              }
          }
      }
--- 1,11 ----
  #include <core.p4>
  control Ing(out bit<32> a) {
      bool b;
      @name("Ing.cond") action cond_0() {
          {
              {
!                 a = (b ? 32w5 : a);
!                 a = (!b ? 32w10 : a);
              }
          }
      }
