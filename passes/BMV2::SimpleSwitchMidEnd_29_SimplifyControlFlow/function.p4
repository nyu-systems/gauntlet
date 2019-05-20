*** dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:22.051670300 +0200
--- dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:22.134623200 +0200
*************** control c(out bit<16> b) {
*** 2,14 ****
      bool hasReturned_0;
      bit<16> retval_0;
      apply {
!         {
!             hasReturned_0 = false;
!             ;
!             if (!hasReturned_0) {
!                 hasReturned_0 = true;
!                 retval_0 = 16w12;
!             }
          }
          b = retval_0;
      }
--- 2,11 ----
      bool hasReturned_0;
      bit<16> retval_0;
      apply {
!         hasReturned_0 = false;
!         if (!hasReturned_0) {
!             hasReturned_0 = true;
!             retval_0 = 16w12;
          }
          b = retval_0;
      }
