*** dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:50.959566500 +0200
--- dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:50.962204100 +0200
*************** struct tuple_0 {
*** 9,19 ****
      bool    field_0;
  }
  control c() {
-     tuple_0 x;
      apply {
          {
-             x.field = 32w10;
-             x.field_0 = false;
          }
      }
  }
--- 9,16 ----
