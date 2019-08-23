--- before_pass
+++ after_pass
@@ -3,14 +3,18 @@ control p() {
     bit<1> x_2;
     bit<1> x_3;
     bit<1> y_1;
-    @name("p.b") action b(in bit<1> x, out bit<1> y) {
+    bit<1> x;
+    bit<1> y;
+    @name("p.b") action b() {
+        x = x_3;
         x_2 = x;
         z_0 = x & x_2;
         y = z_0;
+        y_1 = y;
     }
     apply {
         x_3 = 1w0;
-        b(x_3, y_1);
+        b();
     }
 }
 control simple();
