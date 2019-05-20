*** dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:50.936181200 +0200
--- dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:50.940337100 +0200
*************** struct tuple_0 {
*** 11,17 ****
  control c() {
      tuple_0 x;
      apply {
!         x = { 32w10, false };
      }
  }
  top(c()) main;
--- 11,20 ----
  control c() {
      tuple_0 x;
      apply {
!         {
!             x.field = 32w10;
!             x.field_0 = false;
!         }
      }
  }
  top(c()) main;
