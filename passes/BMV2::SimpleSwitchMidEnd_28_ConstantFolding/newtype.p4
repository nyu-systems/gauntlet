--- before_pass
+++ after_pass
@@ -23,12 +23,10 @@ control c(out B32 x) {
     }
     apply {
         k_0 = 32w0;
-        x = (B32)32w0;
-        if (32w0 == 32w1) 
-            x = 32w2;
+        x = 32w0;
+        ;
         t_0.apply();
-        if (32w0 == (B32)32w0) 
-            x = 32w3;
+        x = 32w3;
     }
 }
 control e(out B32 x);
