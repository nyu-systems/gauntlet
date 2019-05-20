*** dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:49.855480800 +0200
--- dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:59:49.859952500 +0200
*************** control c(out B32 x) {
*** 23,34 ****
      }
      apply {
          k = 32w0;
!         x = (B32)32w0;
!         if (32w0 == 32w1) 
!             x = 32w2;
          t.apply();
!         if (32w0 == (B32)32w0) 
!             x = 32w3;
      }
  }
  control e(out B32 x);
--- 23,32 ----
      }
      apply {
          k = 32w0;
!         x = 32w0;
!         ;
          t.apply();
!         x = 32w3;
      }
  }
  control e(out B32 x);
