*** dumps/p4_16_samples/tuple2.p4/pruned/tuple2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:51.804004400 +0200
--- dumps/p4_16_samples/tuple2.p4/pruned/tuple2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:51.808424400 +0200
*************** struct tuple_0 {
*** 8,14 ****
  control c() {
      tuple_0 x_0;
      apply {
!         x_0 = { 32w10, false };
          f<tuple_0>(x_0);
      }
  }
--- 8,17 ----
  control c() {
      tuple_0 x_0;
      apply {
!         {
!             x_0.field = 32w10;
!             x_0.field_0 = false;
!         }
          f<tuple_0>(x_0);
      }
  }
