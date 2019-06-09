--- before_pass
+++ after_pass
@@ -1,11 +1,7 @@
 extern void f(in bit<16> x, in bool y);
 control c() {
-    bit<16> xv_0;
-    bool b_0;
     apply {
-        xv_0 = 16w0;
-        b_0 = true;
-        f(x = xv_0, y = b_0);
+        f(x = 16w0, y = true);
     }
 }
 control empty();
