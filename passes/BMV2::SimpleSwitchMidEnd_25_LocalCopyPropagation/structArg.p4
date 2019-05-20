*** dumps/p4_16_samples/structArg.p4/pruned/structArg-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:35.646833500 +0200
--- dumps/p4_16_samples/structArg.p4/pruned/structArg-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:35.650800000 +0200
*************** struct S {
*** 2,11 ****
      bit<32> f;
  }
  control caller() {
-     S data;
      apply {
-         data.f = 32w0;
-         data.f = 32w0;
      }
  }
  control none();
--- 2,8 ----
