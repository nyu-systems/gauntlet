*** dumps/p4_16_samples/action_param.p4/pruned/action_param-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:57:46.770443000 +0200
--- dumps/p4_16_samples/action_param.p4/pruned/action_param-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:57:46.796349600 +0200
***************
*** 1,12 ****
  control c(inout bit<32> x) {
!     @name("c.a") action a_0(in bit<32> arg_1) {
          x = arg_1;
      }
      @name("c.t") table t {
          actions = {
!             a_0(32w10);
          }
!         default_action = a_0(32w10);
      }
      apply {
          t.apply();
--- 1,14 ----
  control c(inout bit<32> x) {
!     bit<32> arg_1;
!     @name("c.a") action a_0() {
!         arg_1 = 32w10;
          x = arg_1;
      }
      @name("c.t") table t {
          actions = {
!             a_0();
          }
!         default_action = a_0();
      }
      apply {
          t.apply();
