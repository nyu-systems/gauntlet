*** dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:49.864348200 +0200
--- dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:49.911359700 +0200
*************** control c(out B32 x) {
*** 24,30 ****
      apply {
          k = 32w0;
          x = 32w0;
-         ;
          t.apply();
          x = 32w3;
      }
--- 24,29 ----
