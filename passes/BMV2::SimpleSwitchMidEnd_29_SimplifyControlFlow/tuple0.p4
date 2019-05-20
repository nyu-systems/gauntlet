*** dumps/p4_16_samples/tuple0.p4/pruned/tuple0-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:51.276690600 +0200
--- dumps/p4_16_samples/tuple0.p4/pruned/tuple0-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:51.330575400 +0200
*************** package top(proto _p);
*** 8,17 ****
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
--- 8,15 ----
  control c() {
      tuple_0 x;
      apply {
!         x.field = 32w10;
!         x.field_0 = false;
          f(x);
          f({ 32w20, true });
      }
