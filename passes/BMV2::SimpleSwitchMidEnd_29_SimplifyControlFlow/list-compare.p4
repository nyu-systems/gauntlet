*** dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:38.369654800 +0200
--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:38.433284500 +0200
*************** struct tuple_0 {
*** 10,19 ****
  }
  control test(out bool zout) {
      apply {
-         {
-         }
-         {
-         }
          zout = true;
          zout = true;
      }
--- 10,15 ----
