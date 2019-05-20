*** dumps/p4_16_samples/inline-function.p4/pruned/inline-function-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:33.902100900 +0200
--- dumps/p4_16_samples/inline-function.p4/pruned/inline-function-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:33.931478600 +0200
***************
*** 1,19 ****
  control c(inout bit<32> x) {
      bit<32> tmp_3;
      apply {
          {
!             bit<32> a = x;
!             bit<32> b = x;
!             bool hasReturned_1 = false;
!             bit<32> retval_1;
!             bit<32> tmp_4;
!             bit<32> tmp_5;
              {
!                 bit<32> a_2 = a;
!                 bit<32> b_2 = b;
!                 bool hasReturned_2 = false;
!                 bit<32> retval_2;
!                 bit<32> tmp_6;
                  if (a_2 > b_2) 
                      tmp_6 = b_2;
                  else 
--- 1,25 ----
  control c(inout bit<32> x) {
      bit<32> tmp_3;
+     bit<32> a;
+     bit<32> b;
+     bool hasReturned_1;
+     bit<32> retval_1;
+     bit<32> tmp_4;
+     bit<32> tmp_5;
+     bit<32> a_2;
+     bit<32> b_2;
+     bool hasReturned_2;
+     bit<32> retval_2;
+     bit<32> tmp_6;
      apply {
          {
!             a = x;
!             b = x;
!             hasReturned_1 = false;
              {
!                 a_2 = a;
!                 b_2 = b;
!                 hasReturned_2 = false;
                  if (a_2 > b_2) 
                      tmp_6 = b_2;
                  else 
