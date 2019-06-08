--- before_pass
+++ after_pass
@@ -19,9 +19,9 @@ control c(inout bit<16> p) {
                 ix_1.a = x.a;
                 ix_1.b = x.b;
             }
-            if (ix_1.a < ix_1.b) 
-                x.a = ix_1.a + 16w1;
-            if (ix_1.a > ix_1.b) 
+            if (x.a < x.b) 
+                x.a = x.a + 16w1;
+            if (ix_1.a > x.b) 
                 x.a = ix_1.a + 16w65535;
         }
     };
