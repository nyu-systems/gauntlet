*** dumps/p4_16_samples/action_param.p4/pruned/action_param-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:46.755100800 +0200
--- dumps/p4_16_samples/action_param.p4/pruned/action_param-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:46.759261400 +0200
***************
*** 1,8 ****
  control c(inout bit<32> x) {
-     bit<32> arg_1;
      @name("c.a") action a_0() {
!         arg_1 = 32w10;
!         x = arg_1;
      }
      @name("c.t") table t {
          actions = {
--- 1,6 ----
  control c(inout bit<32> x) {
      @name("c.a") action a_0() {
!         x = 32w10;
      }
      @name("c.t") table t {
          actions = {
