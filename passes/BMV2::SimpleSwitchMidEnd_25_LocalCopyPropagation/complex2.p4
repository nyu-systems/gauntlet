*** dumps/p4_16_samples/complex2.p4/pruned/complex2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:04.955224100 +0200
--- dumps/p4_16_samples/complex2.p4/pruned/complex2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:04.957253100 +0200
*************** header H {
*** 5,15 ****
  control c(inout bit<32> r) {
      H[2] h;
      bit<32> tmp_1;
-     bit<32> tmp_2;
      apply {
          tmp_1 = f(32w2);
!         tmp_2 = tmp_1;
!         h[tmp_2].setValid();
      }
  }
  control simple(inout bit<32> r);
--- 5,13 ----
  control c(inout bit<32> r) {
      H[2] h;
      bit<32> tmp_1;
      apply {
          tmp_1 = f(32w2);
!         h[tmp_1].setValid();
      }
  }
  control simple(inout bit<32> r);
