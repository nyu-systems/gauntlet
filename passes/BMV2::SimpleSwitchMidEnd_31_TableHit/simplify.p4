--- before_pass
+++ after_pass
@@ -27,11 +27,17 @@ control c(out bool x) {
     }
     apply {
         x = true;
-        tmp_2 = t1.apply().hit;
+        if (t1.apply().hit) 
+            tmp_2 = true;
+        else 
+            tmp_2 = false;
         if (!tmp_2) 
             tmp_3 = false;
         else {
-            tmp_4 = t2.apply().hit;
+            if (t2.apply().hit) 
+                tmp_4 = true;
+            else 
+                tmp_4 = false;
             tmp_3 = tmp_4;
         }
         if (tmp_3) 
