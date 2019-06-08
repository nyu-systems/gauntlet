--- before_pass
+++ after_pass
@@ -17,12 +17,12 @@ control c() {
         f(a = 32w2);
         f(b = 16w1);
         f(a = 32w1, b = 16w2);
-        f(b = 16w2, a = 32w1);
+        f(a = 32w1, b = 16w2);
         o.f();
         o.f(a = 32w2);
         o.f(b = 16w1);
         o.f(a = 32w1, b = 16w2);
-        o.f(b = 16w2, a = 32w1);
+        o.f(a = 32w1, b = 16w2);
         z = 32w4294967294;
     }
 }
