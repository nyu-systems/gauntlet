*** dumps/p4_16_samples/inline-switch.p4/pruned/inline-switch-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:34.993518400 +0200
--- dumps/p4_16_samples/inline-switch.p4/pruned/inline-switch-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:35.047396100 +0200
*************** control d(out bit<32> x) {
*** 11,23 ****
          default_action = cinst_a1();
      }
      apply {
!         {
!             switch (cinst_t_0.apply().action_run) {
!                 cinst_a1: 
!                 cinst_a2: {
!                 }
!                 default: {
!                 }
              }
          }
      }
--- 11,21 ----
          default_action = cinst_a1();
      }
      apply {
!         switch (cinst_t_0.apply().action_run) {
!             cinst_a1: 
!             cinst_a2: {
!             }
!             default: {
              }
          }
      }
