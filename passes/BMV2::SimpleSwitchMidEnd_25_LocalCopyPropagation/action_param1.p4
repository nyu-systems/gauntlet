*** dumps/p4_16_samples/action_param1.p4/pruned/action_param1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:47.039739700 +0200
--- dumps/p4_16_samples/action_param1.p4/pruned/action_param1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:47.043225600 +0200
***************
*** 1,8 ****
  control c(inout bit<32> x) {
-     bit<32> arg_1;
      @name("c.a") action a_0() {
!         arg_1 = 32w15;
!         x = arg_1;
      }
      apply {
          a_0();
--- 1,6 ----
  control c(inout bit<32> x) {
      @name("c.a") action a_0() {
!         x = 32w15;
      }
      apply {
          a_0();
