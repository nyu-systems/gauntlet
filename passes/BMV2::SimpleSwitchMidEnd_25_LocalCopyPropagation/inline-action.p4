*** dumps/p4_16_samples/inline-action.p4/pruned/inline-action-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:44.141844200 +0200
--- dumps/p4_16_samples/inline-action.p4/pruned/inline-action-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:44.145426000 +0200
***************
*** 1,16 ****
  control p(inout bit<1> bt) {
-     bit<1> y0_0;
-     bit<1> y0_2;
      @name("p.b") action b_0() {
          {
!             y0_0 = bt;
!             y0_0 = y0_0 | 1w1;
!             bt = y0_0;
          }
          {
!             y0_2 = bt;
!             y0_2 = y0_2 | 1w1;
!             bt = y0_2;
          }
      }
      @name("p.t") table t {
--- 1,10 ----
  control p(inout bit<1> bt) {
      @name("p.b") action b_0() {
          {
!             bt = bt | 1w1;
          }
          {
!             bt = bt | 1w1;
          }
      }
      @name("p.t") table t {
