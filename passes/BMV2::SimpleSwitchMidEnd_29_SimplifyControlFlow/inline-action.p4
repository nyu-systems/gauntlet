*** dumps/p4_16_samples/inline-action.p4/pruned/inline-action-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:57:44.152461800 +0200
--- dumps/p4_16_samples/inline-action.p4/pruned/inline-action-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:57:44.207317600 +0200
***************
*** 1,11 ****
  control p(inout bit<1> bt) {
      @name("p.b") action b_0() {
!         {
!             bt = bt | 1w1;
!         }
!         {
!             bt = bt | 1w1;
!         }
      }
      @name("p.t") table t {
          actions = {
--- 1,7 ----
  control p(inout bit<1> bt) {
      @name("p.b") action b_0() {
!         bt = bt | 1w1;
!         bt = bt | 1w1;
      }
      @name("p.t") table t {
          actions = {
