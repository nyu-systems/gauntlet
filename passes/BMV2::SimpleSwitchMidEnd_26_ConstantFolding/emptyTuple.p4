--- before_pass
+++ after_pass
@@ -6,10 +6,7 @@ control c(out bool b) {
     apply {
         {
         }
-        if (true) 
-            b = true;
-        else 
-            b = false;
+        b = true;
     }
 }
 control e(out bool b);
