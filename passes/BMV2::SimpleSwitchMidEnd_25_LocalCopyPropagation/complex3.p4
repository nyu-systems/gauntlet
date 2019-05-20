*** dumps/p4_16_samples/complex3.p4/pruned/complex3-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:05.256326900 +0200
--- dumps/p4_16_samples/complex3.p4/pruned/complex3-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:05.259119100 +0200
*************** extern bit<32> f(in bit<32> x);
*** 2,13 ****
  control c(inout bit<32> r) {
      bit<32> tmp_2;
      bit<32> tmp_3;
-     bit<32> tmp_4;
      apply {
          tmp_2 = f(32w4);
          tmp_3 = f(32w5);
!         tmp_4 = tmp_2 + tmp_3;
!         r = tmp_4;
      }
  }
  control simple(inout bit<32> r);
--- 2,11 ----
  control c(inout bit<32> r) {
      bit<32> tmp_2;
      bit<32> tmp_3;
      apply {
          tmp_2 = f(32w4);
          tmp_3 = f(32w5);
!         r = tmp_2 + tmp_3;
      }
  }
  control simple(inout bit<32> r);
