*** dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:50.148469700 +0200
--- dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:50.150731200 +0200
*************** typedef Narrow_t Narrow;
*** 3,14 ****
  typedef bit<32> Wide_t;
  typedef Wide_t Wide;
  control c(out bool b) {
-     Wide x;
-     Narrow y;
      apply {
!         x = 32w3;
!         y = (Narrow_t)(Wide_t)x;
!         b = y == 9w10;
      }
  }
  control ctrl(out bool b);
--- 3,10 ----
  typedef bit<32> Wide_t;
  typedef Wide_t Wide;
  control c(out bool b) {
      apply {
!         b = (Narrow_t)(Wide_t)32w3 == 9w10;
      }
  }
  control ctrl(out bool b);
