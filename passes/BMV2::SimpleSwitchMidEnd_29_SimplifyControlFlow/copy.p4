*** dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:09.842032500 +0200
--- dumps/p4_16_samples/copy.p4/pruned/copy-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:09.898494200 +0200
*************** struct S {
*** 3,14 ****
  }
  control c(inout bit<32> b) {
      @name("c.a") action a_0() {
-         {
-         }
-         {
-         }
-         {
-         }
          b = 32w0;
      }
      apply {
--- 3,8 ----
