*** dumps/p4_16_samples/stack2.p4/pruned/stack2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:30.303979200 +0200
--- dumps/p4_16_samples/stack2.p4/pruned/stack2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:30.311031900 +0200
***************
*** 2,11 ****
  header h {
  }
  control c(out bit<32> x) {
-     bit<32> sz;
      apply {
!         sz = 32w4;
!         x = sz;
      }
  }
  control Simpler(out bit<32> x);
--- 2,9 ----
  header h {
  }
  control c(out bit<32> x) {
      apply {
!         x = 32w4;
      }
  }
  control Simpler(out bit<32> x);
