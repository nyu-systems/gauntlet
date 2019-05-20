*** dumps/p4_16_samples/pred.p4/pruned/pred-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:56.262002500 +0200
--- dumps/p4_16_samples/pred.p4/pruned/pred-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:56.266144300 +0200
***************
*** 3,11 ****
  control empty();
  package top(empty e);
  control Ing() {
-     bool b;
      @name("Ing.cond") action cond_0() {
-         b = true;
      }
      apply {
          cond_0();
--- 3,9 ----
