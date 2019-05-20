*** dumps/p4_16_samples/concat.p4/pruned/concat-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:07.728054900 +0200
--- dumps/p4_16_samples/concat.p4/pruned/concat-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:58:07.730266200 +0200
*************** control proto(out bit<32> x);
*** 2,8 ****
  package top(proto _c);
  control c(out bit<32> x) {
      apply {
!         x = 8w0xf ++ 16w0xf ++ 8w0xf + (16w0xf ++ (8w0xf ++ 8w0xf));
      }
  }
  top(c()) main;
--- 2,8 ----
  package top(proto _c);
  control c(out bit<32> x) {
      apply {
!         x = 32w0xf0f1e1e;
      }
  }
  top(c()) main;
