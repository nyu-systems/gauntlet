*** dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_0_CheckTableSize.p4	2019-05-20 16:59:49.804214300 +0200
--- dumps/p4_16_samples/newtype.p4/pruned/newtype-BMV2::SimpleSwitchMidEnd_1_EliminateNewtype.p4	2019-05-20 16:59:49.836826100 +0200
***************
*** 1,6 ****
  #include <core.p4>
  typedef bit<32> B32;
! type bit<32> N32;
  struct S {
      B32 b;
      N32 n;
--- 1,6 ----
  #include <core.p4>
  typedef bit<32> B32;
! typedef bit<32> N32;
  struct S {
      B32 b;
      N32 n;
*************** control c(out B32 x) {
*** 27,36 ****
      }
      apply {
          b_1 = 32w0;
!         n_1 = (N32)b_1;
          k = n_1;
          x = (B32)n_1;
!         n1 = (N32)32w1;
          if (n_1 == n1) 
              x = 32w2;
          s.b = b_1;
--- 27,36 ----
      }
      apply {
          b_1 = 32w0;
!         n_1 = b_1;
          k = n_1;
          x = (B32)n_1;
!         n1 = 32w1;
          if (n_1 == n1) 
              x = 32w2;
          s.b = b_1;
