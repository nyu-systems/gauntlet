--- before_pass
+++ after_pass
@@ -1,14 +1,10 @@
 control c(inout bit<32> x) {
     bit<32> tmp_6;
     apply {
-        {
-            {
-                if (x > x) 
-                    tmp_6 = x;
-                else 
-                    tmp_6 = x;
-            }
-        }
+        if (x > x) 
+            tmp_6 = x;
+        else 
+            tmp_6 = x;
         x = x + tmp_6;
     }
 }
