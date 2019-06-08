--- before_pass
+++ after_pass
@@ -5,7 +5,7 @@ control c() {
     apply {
         xv = 16w0;
         b = true;
-        f(y = b, x = xv);
+        f(x = xv, y = b);
     }
 }
 control empty();
