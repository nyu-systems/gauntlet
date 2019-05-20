*** dumps/p4_16_samples/action-bind.p4/pruned/action-bind-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:44.767156900 +0200
--- dumps/p4_16_samples/action-bind.p4/pruned/action-bind-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:44.769440300 +0200
***************
*** 1,9 ****
  control c(inout bit<32> x) {
-     bit<32> b;
      @name("c.a") action a_0(bit<32> d) {
!         b = x;
!         b = d;
!         x = b;
      }
      @name("c.t") table t {
          actions = {
--- 1,6 ----
  control c(inout bit<32> x) {
      @name("c.a") action a_0(bit<32> d) {
!         x = d;
      }
      @name("c.t") table t {
          actions = {
