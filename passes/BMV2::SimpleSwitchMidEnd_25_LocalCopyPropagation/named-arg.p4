--- before_pass
+++ after_pass
@@ -1,11 +1,7 @@
 extern void f(in bit<16> x, in bool y);
 control c() {
-    bit<16> xv;
-    bool b;
     apply {
-        xv = 16w0;
-        b = true;
-        f(x = xv, y = b);
+        f(x = 16w0, y = true);
     }
 }
 control empty();
