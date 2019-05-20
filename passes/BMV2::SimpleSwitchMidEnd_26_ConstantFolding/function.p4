*** dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:22.037965000 +0200
--- dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:58:22.041998600 +0200
*************** control c(out bit<16> b) {
*** 4,13 ****
      apply {
          {
              hasReturned_0 = false;
!             if (16w10 > 16w12) {
!                 hasReturned_0 = true;
!                 retval_0 = 16w10;
!             }
              if (!hasReturned_0) {
                  hasReturned_0 = true;
                  retval_0 = 16w12;
--- 4,10 ----
      apply {
          {
              hasReturned_0 = false;
!             ;
              if (!hasReturned_0) {
                  hasReturned_0 = true;
                  retval_0 = 16w12;
