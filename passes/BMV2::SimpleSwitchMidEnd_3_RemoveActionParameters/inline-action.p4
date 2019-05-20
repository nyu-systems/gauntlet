*** dumps/p4_16_samples/inline-action.p4/pruned/inline-action-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:57:44.154588000 +0200
--- dumps/p4_16_samples/inline-action.p4/pruned/inline-action-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:57:44.177230900 +0200
***************
*** 1,12 ****
  control p(inout bit<1> bt) {
      @name("p.b") action b_0() {
          {
!             bit<1> y0_0 = bt;
              y0_0 = y0_0 | 1w1;
              bt = y0_0;
          }
          {
!             bit<1> y0_2 = bt;
              y0_2 = y0_2 | 1w1;
              bt = y0_2;
          }
--- 1,14 ----
  control p(inout bit<1> bt) {
+     bit<1> y0_0;
+     bit<1> y0_2;
      @name("p.b") action b_0() {
          {
!             y0_0 = bt;
              y0_0 = y0_0 | 1w1;
              bt = y0_0;
          }
          {
!             y0_2 = bt;
              y0_2 = y0_2 | 1w1;
              bt = y0_2;
          }
