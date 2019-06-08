--- dumps/pruned/decl2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:29.497542100 +0200
+++ dumps/pruned/decl2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:29.500293100 +0200
@@ -1,16 +1,6 @@
 control p() {
-    bit<1> z;
-    bit<1> x;
     bit<1> x_1;
-    bit<1> y;
-    bit<1> x_2;
-    bit<1> y_1;
     @name("p.b") action b_0() {
-        x_2 = x_1;
-        x = x_2;
-        z = x_2 & x;
-        y_1 = z;
-        y = y_1;
     }
     apply {
         x_1 = 1w0;
