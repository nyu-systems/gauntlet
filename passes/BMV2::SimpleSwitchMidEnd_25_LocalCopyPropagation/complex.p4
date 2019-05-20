*** dumps/p4_16_samples/complex.p4/pruned/complex-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:04.084312900 +0200
--- dumps/p4_16_samples/complex.p4/pruned/complex-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:04.086970900 +0200
***************
*** 1,12 ****
  extern bit<32> f(in bit<32> x);
  control c(inout bit<32> r) {
      bit<32> tmp_2;
-     bit<32> tmp_3;
      bit<32> tmp_4;
      apply {
          tmp_2 = f(32w5);
!         tmp_3 = tmp_2;
!         tmp_4 = f(tmp_3);
          r = tmp_4;
      }
  }
--- 1,10 ----
  extern bit<32> f(in bit<32> x);
  control c(inout bit<32> r) {
      bit<32> tmp_2;
      bit<32> tmp_4;
      apply {
          tmp_2 = f(32w5);
!         tmp_4 = f(tmp_2);
          r = tmp_4;
      }
  }
