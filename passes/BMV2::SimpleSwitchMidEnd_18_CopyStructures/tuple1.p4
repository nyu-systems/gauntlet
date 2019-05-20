*** dumps/p4_16_samples/tuple1.p4/pruned/tuple1-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:51.528307200 +0200
--- dumps/p4_16_samples/tuple1.p4/pruned/tuple1-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:51.533690500 +0200
*************** struct tuple_0 {
*** 8,14 ****
  control c() {
      tuple_0 x;
      apply {
!         x = { 32w10, false };
          f<tuple_0>(x);
      }
  }
--- 8,17 ----
  control c() {
      tuple_0 x;
      apply {
!         {
!             x.field = 32w10;
!             x.field_0 = false;
!         }
          f<tuple_0>(x);
      }
  }
