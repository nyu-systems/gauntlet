--- before_pass
+++ after_pass
@@ -16,7 +16,9 @@ control Ing(inout Headers headers, inout
     S s;
     @name("Ing.r") register<S>(32w100) r;
     apply {
-        s = { 32w0 };
+        {
+            s.f = 32w0;
+        }
         r.write(32w0, s);
     }
 }
