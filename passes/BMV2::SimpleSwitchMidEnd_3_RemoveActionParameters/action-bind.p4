*** dumps/p4_16_samples/action-bind.p4/pruned/action-bind-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:57:44.832074200 +0200
--- dumps/p4_16_samples/action-bind.p4/pruned/action-bind-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:57:44.804675900 +0200
***************
*** 1,12 ****
  control c(inout bit<32> x) {
!     @name("c.a") action a_0(inout bit<32> b, bit<32> d) {
          b = d;
      }
      @name("c.t") table t {
          actions = {
!             a_0(x);
          }
!         default_action = a_0(x, 32w0);
      }
      apply {
          t.apply();
--- 1,15 ----
  control c(inout bit<32> x) {
!     bit<32> b;
!     @name("c.a") action a_0(bit<32> d) {
!         b = x;
          b = d;
+         x = b;
      }
      @name("c.t") table t {
          actions = {
!             a_0();
          }
!         default_action = a_0(32w0);
      }
      apply {
          t.apply();
