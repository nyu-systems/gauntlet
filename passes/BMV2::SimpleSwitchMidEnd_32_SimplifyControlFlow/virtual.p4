--- before_pass
+++ after_pass
@@ -15,10 +15,8 @@ control c(inout bit<16> p) {
         }
         void g(inout data x) {
             data ix_0;
-            {
-                ix_0.a = x.a;
-                ix_0.b = x.b;
-            }
+            ix_0.a = x.a;
+            ix_0.b = x.b;
             if (x.a < x.b) 
                 x.a = x.a + 16w1;
             if (ix_0.a > x.b) 
