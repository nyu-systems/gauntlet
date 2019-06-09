--- before_pass
+++ after_pass
@@ -1,14 +1,10 @@
 control c(inout bit<32> x) {
     bit<32> tmp_2;
     apply {
-        {
-            {
-                if (x > x) 
-                    tmp_2 = x;
-                else 
-                    tmp_2 = x;
-            }
-        }
+        if (x > x) 
+            tmp_2 = x;
+        else 
+            tmp_2 = x;
         x = x + tmp_2;
     }
 }
