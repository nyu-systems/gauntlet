--- before_pass
+++ after_pass
@@ -17,12 +17,12 @@ control c() {
         f(a = 32w2);
         f(b = 16w1);
         f(a = 32w1, b = 16w2);
-        f(b = 16w2, a = 32w1);
+        f(a = 32w1, b = 16w2);
         o_0.f();
         o_0.f(a = 32w2);
         o_0.f(b = 16w1);
         o_0.f(a = 32w1, b = 16w2);
-        o_0.f(b = 16w2, a = 32w1);
+        o_0.f(a = 32w1, b = 16w2);
         z_0 = 32w4294967294;
     }
 }
