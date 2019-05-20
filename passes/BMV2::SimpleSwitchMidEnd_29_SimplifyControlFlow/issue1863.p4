*** dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:00.187702700 +0200
--- dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:00.191737500 +0200
*************** struct S {
*** 4,13 ****
  }
  control c(out bit<1> b) {
      apply {
-         {
-         }
-         {
-         }
          b = 1w1;
      }
  }
--- 4,9 ----
