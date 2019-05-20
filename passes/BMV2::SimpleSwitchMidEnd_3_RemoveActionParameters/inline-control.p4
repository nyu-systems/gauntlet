*** dumps/p4_16_samples/inline-control.p4/pruned/inline-control-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:58:33.288772600 +0200
--- dumps/p4_16_samples/inline-control.p4/pruned/inline-control-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:58:33.313934600 +0200
*************** extern Y {
*** 3,10 ****
      bit<32> get();
  }
  control d(out bit<32> x) {
-     @name("d.cinst.y") Y(32w16) cinst_y_0;
      bit<32> cinst_tmp_0;
      apply {
          cinst_tmp_0 = cinst_y_0.get();
          x = cinst_tmp_0;
--- 3,10 ----
      bit<32> get();
  }
  control d(out bit<32> x) {
      bit<32> cinst_tmp_0;
+     @name("d.cinst.y") Y(32w16) cinst_y_0;
      apply {
          cinst_tmp_0 = cinst_y_0.get();
          x = cinst_tmp_0;
