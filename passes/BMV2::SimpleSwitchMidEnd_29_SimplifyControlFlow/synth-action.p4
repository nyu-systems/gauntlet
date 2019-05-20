*** dumps/p4_16_samples/synth-action.p4/pruned/synth-action-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:45.414738100 +0200
--- dumps/p4_16_samples/synth-action.p4/pruned/synth-action-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:45.488057800 +0200
***************
*** 1,10 ****
  control c(inout bit<32> x) {
      apply {
          x = 32w10;
!         {
!             x = 32w12;
!             x = 32w6;
!         }
      }
  }
  control n(inout bit<32> x);
--- 1,8 ----
  control c(inout bit<32> x) {
      apply {
          x = 32w10;
!         x = 32w12;
!         x = 32w6;
      }
  }
  control n(inout bit<32> x);
