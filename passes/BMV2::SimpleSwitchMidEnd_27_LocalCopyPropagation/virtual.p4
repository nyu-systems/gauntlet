--- before_pass
+++ after_pass
@@ -19,9 +19,9 @@ control c(inout bit<16> p) {
                 ix_0.a = x.a;
                 ix_0.b = x.b;
             }
-            if (ix_0.a < ix_0.b) 
-                x.a = ix_0.a + 16w1;
-            if (ix_0.a > ix_0.b) 
+            if (x.a < x.b) 
+                x.a = x.a + 16w1;
+            if (ix_0.a > x.b) 
                 x.a = ix_0.a + 16w65535;
         }
     };
