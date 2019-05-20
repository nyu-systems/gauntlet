*** dumps/p4_16_samples/inline-function.p4/pruned/inline-function-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:33.899719700 +0200
--- dumps/p4_16_samples/inline-function.p4/pruned/inline-function-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:33.959364100 +0200
***************
*** 1,14 ****
  control c(inout bit<32> x) {
      bit<32> tmp_6;
      apply {
!         {
!             {
!                 if (x > x) 
!                     tmp_6 = x;
!                 else 
!                     tmp_6 = x;
!             }
!         }
          x = x + tmp_6;
      }
  }
--- 1,10 ----
  control c(inout bit<32> x) {
      bit<32> tmp_6;
      apply {
!         if (x > x) 
!             tmp_6 = x;
!         else 
!             tmp_6 = x;
          x = x + tmp_6;
      }
  }
