*** dumps/p4_16_samples/concat.p4/pruned/concat-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:07.725811700 +0200
--- dumps/p4_16_samples/concat.p4/pruned/concat-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:07.728054900 +0200
***************
*** 1,12 ****
  control proto(out bit<32> x);
  package top(proto _c);
  control c(out bit<32> x) {
-     bit<8> a;
-     bit<16> b;
      apply {
!         a = 8w0xf;
!         b = 16w0xf;
!         x = a ++ b ++ a + (b ++ (a ++ a));
      }
  }
  top(c()) main;
--- 1,8 ----
  control proto(out bit<32> x);
  package top(proto _c);
  control c(out bit<32> x) {
      apply {
!         x = 8w0xf ++ 16w0xf ++ 8w0xf + (16w0xf ++ (8w0xf ++ 8w0xf));
      }
  }
  top(c()) main;
