*** dumps/p4_16_samples/inline-switch.p4/pruned/inline-switch-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:34.996481000 +0200
--- dumps/p4_16_samples/inline-switch.p4/pruned/inline-switch-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:35.021109500 +0200
***************
*** 1,4 ****
--- 1,5 ----
  control d(out bit<32> x) {
+     bool cinst_hasReturned_0;
      @name("d.cinst.a1") action cinst_a1() {
      }
      @name("d.cinst.a2") action cinst_a2() {
*************** control d(out bit<32> x) {
*** 12,18 ****
      }
      apply {
          {
!             bool cinst_hasReturned_0 = false;
              switch (cinst_t_0.apply().action_run) {
                  cinst_a1: 
                  cinst_a2: {
--- 13,19 ----
      }
      apply {
          {
!             cinst_hasReturned_0 = false;
              switch (cinst_t_0.apply().action_run) {
                  cinst_a1: 
                  cinst_a2: {
