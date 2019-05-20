*** dumps/p4_16_samples/exit1.p4/pruned/exit1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:17.472389600 +0200
--- dumps/p4_16_samples/exit1.p4/pruned/exit1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:58:17.475018800 +0200
***************
*** 1,9 ****
  control ctrl() {
      apply {
!         if (32w0 == 32w0) 
!             exit;
!         else 
!             exit;
      }
  }
  control noop();
--- 1,6 ----
  control ctrl() {
      apply {
!         exit;
      }
  }
  control noop();
