*** dumps/p4_16_samples/inline-control1.p4/pruned/inline-control1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:33.572593700 +0200
--- dumps/p4_16_samples/inline-control1.p4/pruned/inline-control1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:33.576996700 +0200
*************** extern Y {
*** 3,19 ****
      bit<32> get();
  }
  control d(out bit<32> x) {
-     bit<32> y;
-     bit<32> x_1;
      bit<32> cinst_tmp_0;
      @name("d.cinst.y") Y(32w16) cinst_y_0;
      apply {
          cinst_tmp_0 = cinst_y_0.get();
!         x_1 = cinst_tmp_0;
!         x = x_1;
          cinst_tmp_0 = cinst_y_0.get();
-         x_1 = cinst_tmp_0;
-         y = x_1;
      }
  }
  control dproto(out bit<32> x);
--- 3,14 ----
      bit<32> get();
  }
  control d(out bit<32> x) {
      bit<32> cinst_tmp_0;
      @name("d.cinst.y") Y(32w16) cinst_y_0;
      apply {
          cinst_tmp_0 = cinst_y_0.get();
!         x = cinst_tmp_0;
          cinst_tmp_0 = cinst_y_0.get();
      }
  }
  control dproto(out bit<32> x);
