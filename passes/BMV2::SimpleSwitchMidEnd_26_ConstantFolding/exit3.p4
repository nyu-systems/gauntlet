*** dumps/p4_16_samples/exit3.p4/pruned/exit3-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:18.037928500 +0200
--- dumps/p4_16_samples/exit3.p4/pruned/exit3-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:58:18.042906700 +0200
*************** control ctrl(out bit<32> c) {
*** 10,19 ****
      }
      apply {
          c = 32w2;
!         if (32w0 == 32w0) 
!             t.apply();
!         else 
!             t.apply();
          c = 32w5;
      }
  }
--- 10,16 ----
      }
      apply {
          c = 32w2;
!         t.apply();
          c = 32w5;
      }
  }
