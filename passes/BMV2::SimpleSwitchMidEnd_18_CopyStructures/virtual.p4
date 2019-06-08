--- before_pass
+++ after_pass
@@ -15,7 +15,10 @@ control c(inout bit<16> p) {
         }
         void g(inout data x) {
             data ix_1;
-            ix_1 = x;
+            {
+                ix_1.a = x.a;
+                ix_1.b = x.b;
+            }
             if (ix_1.a < ix_1.b) 
                 x.a = ix_1.a + 16w1;
             if (ix_1.a > ix_1.b) 
