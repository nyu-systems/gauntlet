*** dumps/p4_16_samples/tuple0.p4/pruned/tuple0-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:51.238571100 +0200
--- dumps/p4_16_samples/tuple0.p4/pruned/tuple0-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:51.244022700 +0200
*************** package top(proto _p);
*** 8,14 ****
  control c() {
      tuple_0 x;
      apply {
!         x = { 32w10, false };
          f(x);
          f({ 32w20, true });
      }
--- 8,17 ----
  control c() {
      tuple_0 x;
      apply {
!         {
!             x.field = 32w10;
!             x.field_0 = false;
!         }
          f(x);
          f({ 32w20, true });
      }
