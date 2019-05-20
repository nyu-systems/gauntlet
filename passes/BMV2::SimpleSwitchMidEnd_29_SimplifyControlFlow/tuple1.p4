*** dumps/p4_16_samples/tuple1.p4/pruned/tuple1-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:51.562887100 +0200
--- dumps/p4_16_samples/tuple1.p4/pruned/tuple1-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:51.615300000 +0200
*************** struct tuple_0 {
*** 8,17 ****
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
--- 8,15 ----
  control c() {
      tuple_0 x;
      apply {
!         x.field = 32w10;
!         x.field_0 = false;
          f<tuple_0>(x);
      }
  }
