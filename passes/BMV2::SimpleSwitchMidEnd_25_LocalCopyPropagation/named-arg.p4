*** dumps/p4_16_samples/named-arg.p4/pruned/named-arg-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:47.769502100 +0200
--- dumps/p4_16_samples/named-arg.p4/pruned/named-arg-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:47.771825800 +0200
***************
*** 1,11 ****
  extern void f(in bit<16> x, in bool y);
  control c() {
-     bit<16> xv;
-     bool b;
      apply {
!         xv = 16w0;
!         b = true;
!         f(x = xv, y = b);
      }
  }
  control empty();
--- 1,7 ----
  extern void f(in bit<16> x, in bool y);
  control c() {
      apply {
!         f(x = 16w0, y = true);
      }
  }
  control empty();
