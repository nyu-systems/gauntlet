*** dumps/p4_16_samples/after-return.p4/pruned/after-return-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:47.588083800 +0200
--- dumps/p4_16_samples/after-return.p4/pruned/after-return-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:47.590552500 +0200
***************
*** 1,13 ****
  control ctrl() {
-     bit<32> a;
-     bool hasReturned_0;
      apply {
-         hasReturned_0 = false;
-         a = 32w0;
-         if (a == 32w0) 
-             hasReturned_0 = true;
-         else 
-             hasReturned_0 = true;
      }
  }
  control noop();
--- 1,5 ----
