--- dumps/p4_16_samples/inline.p4/pruned/inline-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:04.380758100 +0200
+++ dumps/p4_16_samples/inline.p4/pruned/inline-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:04.382630300 +0200
@@ -1,28 +1,11 @@
 control p(out bit<1> y) {
-    bit<1> x;
-    bit<1> z;
     bit<1> x_3;
-    bit<1> x0_0;
-    bit<1> y0_0;
-    bit<1> x0_2;
-    bit<1> y0_2;
-    bit<1> x_0;
-    bit<1> y_1;
     @name("p.b") action b_0() {
-        x_0 = x_3;
         {
-            x0_0 = x_0;
-            x = x0_0;
-            y0_0 = x0_0 & x;
-            z = y0_0;
         }
         {
-            x0_2 = z & z;
-            x = x0_2;
-            y0_2 = x0_2 & x;
-            y_1 = y0_2;
         }
-        y = y_1;
+        y = x_3 & x_3 & (x_3 & x_3) & (x_3 & x_3 & (x_3 & x_3));
     }
     apply {
         x_3 = 1w1;
