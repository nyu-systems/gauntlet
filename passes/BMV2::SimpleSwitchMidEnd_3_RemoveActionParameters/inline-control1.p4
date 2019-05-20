*** dumps/p4_16_samples/inline-control1.p4/pruned/inline-control1-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:33.587888800 +0200
--- dumps/p4_16_samples/inline-control1.p4/pruned/inline-control1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:33.619853200 +0200
*************** extern Y {
*** 5,12 ****
  control d(out bit<32> x) {
      bit<32> y;
      bit<32> x_1;
-     @name("d.cinst.y") Y(32w16) cinst_y_0;
      bit<32> cinst_tmp_0;
      apply {
          cinst_tmp_0 = cinst_y_0.get();
          x_1 = cinst_tmp_0;
--- 5,12 ----
  control d(out bit<32> x) {
      bit<32> y;
      bit<32> x_1;
      bit<32> cinst_tmp_0;
+     @name("d.cinst.y") Y(32w16) cinst_y_0;
      apply {
          cinst_tmp_0 = cinst_y_0.get();
          x_1 = cinst_tmp_0;
