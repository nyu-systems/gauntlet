*** dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:50.150731200 +0200
--- dumps/p4_16_samples/newtype1.p4/pruned/newtype1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:59:50.153066900 +0200
*************** typedef bit<32> Wide_t;
*** 4,10 ****
  typedef Wide_t Wide;
  control c(out bool b) {
      apply {
!         b = (Narrow_t)(Wide_t)32w3 == 9w10;
      }
  }
  control ctrl(out bool b);
--- 4,10 ----
  typedef Wide_t Wide;
  control c(out bool b) {
      apply {
!         b = false;
      }
  }
  control ctrl(out bool b);
