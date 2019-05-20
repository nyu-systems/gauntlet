*** dumps/p4_16_samples/exit2.p4/pruned/exit2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:17.756100900 +0200
--- dumps/p4_16_samples/exit2.p4/pruned/exit2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:58:17.758211100 +0200
*************** control ctrl(out bit<32> c) {
*** 7,16 ****
      }
      apply {
          c = 32w2;
!         if (32w0 == 32w0) 
!             e_0();
!         else 
!             e_2();
          c = 32w5;
      }
  }
--- 7,13 ----
      }
      apply {
          c = 32w2;
!         e_0();
          c = 32w5;
      }
  }
