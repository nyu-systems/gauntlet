--- before_pass
+++ after_pass
@@ -2,13 +2,10 @@ control c(out bit<16> b) {
     bool hasReturned;
     bit<16> retval;
     apply {
-        {
-            hasReturned = false;
-            ;
-            if (!hasReturned) {
-                hasReturned = true;
-                retval = 16w12;
-            }
+        hasReturned = false;
+        if (!hasReturned) {
+            hasReturned = true;
+            retval = 16w12;
         }
         b = retval;
     }
