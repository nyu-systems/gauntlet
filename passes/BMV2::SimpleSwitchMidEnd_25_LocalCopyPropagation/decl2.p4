*** dumps/p4_16_samples/decl2.p4/pruned/decl2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:10.687140900 +0200
--- dumps/p4_16_samples/decl2.p4/pruned/decl2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:58:10.691676200 +0200
***************
*** 1,16 ****
  control p() {
-     bit<1> z;
-     bit<1> x;
      bit<1> x_1;
-     bit<1> y;
-     bit<1> x_2;
-     bit<1> y_1;
      @name("p.b") action b_0() {
-         x_2 = x_1;
-         x = x_2;
-         z = x_2 & x;
-         y_1 = z;
-         y = y_1;
      }
      apply {
          x_1 = 1w0;
--- 1,6 ----
