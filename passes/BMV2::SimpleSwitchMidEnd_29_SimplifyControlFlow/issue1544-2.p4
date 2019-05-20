*** dumps/p4_16_samples/issue1544-2.p4/pruned/issue1544-2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:48.317886400 +0200
--- dumps/p4_16_samples/issue1544-2.p4/pruned/issue1544-2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:48.320633600 +0200
*************** control c(inout bit<32> x) {
*** 2,24 ****
      bit<32> tmp_6;
      bit<32> tmp_10;
      apply {
!         {
!             if (x > x + 32w1) 
!                 tmp_10 = x + 32w1;
!             else 
!                 tmp_10 = x;
!         }
          tmp_6 = tmp_10;
!         {
!             if (x > x + 32w4294967295) 
!                 tmp_10 = x + 32w4294967295;
!             else 
!                 tmp_10 = x;
!         }
!         {
!             if (!(tmp_6 > tmp_10)) 
!                 tmp_10 = tmp_6;
!         }
          x = tmp_10;
      }
  }
--- 2,18 ----
      bit<32> tmp_6;
      bit<32> tmp_10;
      apply {
!         if (x > x + 32w1) 
!             tmp_10 = x + 32w1;
!         else 
!             tmp_10 = x;
          tmp_6 = tmp_10;
!         if (x > x + 32w4294967295) 
!             tmp_10 = x + 32w4294967295;
!         else 
!             tmp_10 = x;
!         if (!(tmp_6 > tmp_10)) 
!             tmp_10 = tmp_6;
          x = tmp_10;
      }
  }
