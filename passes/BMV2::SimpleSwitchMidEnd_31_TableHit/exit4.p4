--- before_pass
+++ after_pass
@@ -10,7 +10,10 @@ control ctrl() {
         default_action = e_0();
     }
     apply {
-        tmp_0 = t.apply().hit;
+        if (t.apply().hit) 
+            tmp_0 = true;
+        else 
+            tmp_0 = false;
         if (tmp_0) 
             t.apply();
         else 
