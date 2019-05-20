*** dumps/p4_16_samples/issue1544-2.p4/pruned/issue1544-2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:48.369153400 +0200
--- dumps/p4_16_samples/issue1544-2.p4/pruned/issue1544-2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:48.343124600 +0200
*************** control c(inout bit<32> x) {
*** 4,16 ****
      bit<32> tmp_7;
      bit<32> tmp_8;
      bit<32> tmp_9;
      apply {
          {
!             bit<32> a = x;
!             bit<32> b = x + 32w1;
!             bool hasReturned_0 = false;
!             bit<32> retval_0;
!             bit<32> tmp_10;
              if (a > b) 
                  tmp_10 = b;
              else 
--- 4,23 ----
      bit<32> tmp_7;
      bit<32> tmp_8;
      bit<32> tmp_9;
+     bit<32> a;
+     bit<32> b;
+     bool hasReturned_0;
+     bit<32> retval_0;
+     bit<32> tmp_10;
+     bit<32> a_3;
+     bit<32> b_3;
+     bit<32> a_4;
+     bit<32> b_4;
      apply {
          {
!             a = x;
!             b = x + 32w1;
!             hasReturned_0 = false;
              if (a > b) 
                  tmp_10 = b;
              else 
*************** control c(inout bit<32> x) {
*** 21,31 ****
          }
          tmp_6 = tmp_5;
          {
!             bit<32> a_3 = x;
!             bit<32> b_3 = x + 32w4294967295;
!             bool hasReturned_0 = false;
!             bit<32> retval_0;
!             bit<32> tmp_10;
              if (a_3 > b_3) 
                  tmp_10 = b_3;
              else 
--- 28,36 ----
          }
          tmp_6 = tmp_5;
          {
!             a_3 = x;
!             b_3 = x + 32w4294967295;
!             hasReturned_0 = false;
              if (a_3 > b_3) 
                  tmp_10 = b_3;
              else 
*************** control c(inout bit<32> x) {
*** 36,46 ****
          }
          tmp_8 = tmp_7;
          {
!             bit<32> a_4 = tmp_6;
!             bit<32> b_4 = tmp_8;
!             bool hasReturned_0 = false;
!             bit<32> retval_0;
!             bit<32> tmp_10;
              if (a_4 > b_4) 
                  tmp_10 = b_4;
              else 
--- 41,49 ----
          }
          tmp_8 = tmp_7;
          {
!             a_4 = tmp_6;
!             b_4 = tmp_8;
!             hasReturned_0 = false;
              if (a_4 > b_4) 
                  tmp_10 = b_4;
              else 
