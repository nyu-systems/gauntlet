*** dumps/p4_16_samples/exit2.p4/pruned/exit2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:17.754290100 +0200
--- dumps/p4_16_samples/exit2.p4/pruned/exit2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:17.756100900 +0200
***************
*** 1,5 ****
  control ctrl(out bit<32> c) {
-     bit<32> a;
      @name("ctrl.e") action e_0() {
          exit;
      }
--- 1,4 ----
*************** control ctrl(out bit<32> c) {
*** 7,15 ****
          exit;
      }
      apply {
-         a = 32w0;
          c = 32w2;
!         if (a == 32w0) 
              e_0();
          else 
              e_2();
--- 6,13 ----
          exit;
      }
      apply {
          c = 32w2;
!         if (32w0 == 32w0) 
              e_0();
          else 
              e_2();
