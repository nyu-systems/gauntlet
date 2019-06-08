--- before_pass
+++ after_pass
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
