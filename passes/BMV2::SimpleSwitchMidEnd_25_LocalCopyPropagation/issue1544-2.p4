*** dumps/p4_16_samples/issue1544-2.p4/pruned/issue1544-2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:48.305496100 +0200
--- dumps/p4_16_samples/issue1544-2.p4/pruned/issue1544-2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:48.307926800 +0200
***************
*** 1,58 ****
  control c(inout bit<32> x) {
-     bit<32> tmp_5;
      bit<32> tmp_6;
-     bit<32> tmp_7;
-     bit<32> tmp_8;
-     bit<32> tmp_9;
-     bit<32> a;
-     bit<32> b;
-     bool hasReturned_0;
-     bit<32> retval_0;
      bit<32> tmp_10;
-     bit<32> a_3;
-     bit<32> b_3;
-     bit<32> a_4;
-     bit<32> b_4;
      apply {
          {
!             a = x;
!             b = x + 32w1;
!             hasReturned_0 = false;
!             if (a > b) 
!                 tmp_10 = b;
              else 
!                 tmp_10 = a;
!             hasReturned_0 = true;
!             retval_0 = tmp_10;
!             tmp_5 = retval_0;
          }
!         tmp_6 = tmp_5;
          {
!             a_3 = x;
!             b_3 = x + 32w4294967295;
!             hasReturned_0 = false;
!             if (a_3 > b_3) 
!                 tmp_10 = b_3;
              else 
!                 tmp_10 = a_3;
!             hasReturned_0 = true;
!             retval_0 = tmp_10;
!             tmp_7 = retval_0;
          }
-         tmp_8 = tmp_7;
          {
!             a_4 = tmp_6;
!             b_4 = tmp_8;
!             hasReturned_0 = false;
!             if (a_4 > b_4) 
!                 tmp_10 = b_4;
!             else 
!                 tmp_10 = a_4;
!             hasReturned_0 = true;
!             retval_0 = tmp_10;
!             tmp_9 = retval_0;
          }
!         x = tmp_9;
      }
  }
  control ctr(inout bit<32> x);
--- 1,25 ----
  control c(inout bit<32> x) {
      bit<32> tmp_6;
      bit<32> tmp_10;
      apply {
          {
!             if (x > x + 32w1) 
!                 tmp_10 = x + 32w1;
              else 
!                 tmp_10 = x;
          }
!         tmp_6 = tmp_10;
          {
!             if (x > x + 32w4294967295) 
!                 tmp_10 = x + 32w4294967295;
              else 
!                 tmp_10 = x;
          }
          {
!             if (!(tmp_6 > tmp_10)) 
!                 tmp_10 = tmp_6;
          }
!         x = tmp_10;
      }
  }
  control ctr(inout bit<32> x);
