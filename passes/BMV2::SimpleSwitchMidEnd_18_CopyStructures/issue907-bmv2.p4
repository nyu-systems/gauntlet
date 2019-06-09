--- before_pass
+++ after_pass
@@ -16,7 +16,9 @@ control Ing(inout Headers headers, inout
     S s_0;
     @name("Ing.r") register<S>(32w100) r_0;
     apply {
-        s_0 = { 32w0 };
+        {
+            s_0.f = 32w0;
+        }
         r_0.write(32w0, s_0);
     }
 }
