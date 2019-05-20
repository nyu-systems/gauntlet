*** dumps/p4_16_samples/after-return.p4/pruned/after-return-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:57:47.610632300 +0200
--- dumps/p4_16_samples/after-return.p4/pruned/after-return-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:57:47.633979200 +0200
***************
*** 1,7 ****
  control ctrl() {
      bit<32> a;
      apply {
!         bool hasReturned_0 = false;
          a = 32w0;
          if (a == 32w0) 
              hasReturned_0 = true;
--- 1,8 ----
  control ctrl() {
      bit<32> a;
+     bool hasReturned_0;
      apply {
!         hasReturned_0 = false;
          a = 32w0;
          if (a == 32w0) 
              hasReturned_0 = true;
