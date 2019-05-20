*** dumps/p4_16_samples/inline-switch.p4/pruned/inline-switch-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:34.981206600 +0200
--- dumps/p4_16_samples/inline-switch.p4/pruned/inline-switch-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:34.983479400 +0200
***************
*** 1,5 ****
  control d(out bit<32> x) {
-     bool cinst_hasReturned_0;
      @name("d.cinst.a1") action cinst_a1() {
      }
      @name("d.cinst.a2") action cinst_a2() {
--- 1,4 ----
*************** control d(out bit<32> x) {
*** 13,26 ****
      }
      apply {
          {
-             cinst_hasReturned_0 = false;
              switch (cinst_t_0.apply().action_run) {
                  cinst_a1: 
                  cinst_a2: {
-                     cinst_hasReturned_0 = true;
                  }
                  default: {
-                     cinst_hasReturned_0 = true;
                  }
              }
          }
--- 12,22 ----
