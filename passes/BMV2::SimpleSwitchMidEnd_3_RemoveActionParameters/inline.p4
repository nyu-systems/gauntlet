--- dumps/p4_16_samples/inline.p4/pruned/inline-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:30:04.392684900 +0200
+++ dumps/p4_16_samples/inline.p4/pruned/inline-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:30:04.419326800 +0200
@@ -2,25 +2,31 @@ control p(out bit<1> y) {
     bit<1> x;
     bit<1> z;
     bit<1> x_3;
-    @name("p.b") action b_0(in bit<1> x_0, out bit<1> y_1) {
+    bit<1> x0_0;
+    bit<1> y0_0;
+    bit<1> x0_2;
+    bit<1> y0_2;
+    bit<1> x_0;
+    bit<1> y_1;
+    @name("p.b") action b_0() {
+        x_0 = x_3;
         {
-            bit<1> x0_0 = x_0;
-            bit<1> y0_0;
+            x0_0 = x_0;
             x = x0_0;
             y0_0 = x0_0 & x;
             z = y0_0;
         }
         {
-            bit<1> x0_2 = z & z;
-            bit<1> y0_2;
+            x0_2 = z & z;
             x = x0_2;
             y0_2 = x0_2 & x;
             y_1 = y0_2;
         }
+        y = y_1;
     }
     apply {
         x_3 = 1w1;
-        b_0(x_3, y);
+        b_0();
     }
 }
 control simple(out bit<1> y);
