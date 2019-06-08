--- before_pass
+++ after_pass
@@ -2,13 +2,10 @@ control c(out bit<16> b) {
     bool hasReturned_0;
     bit<16> retval_0;
     apply {
-        {
-            hasReturned_0 = false;
-            ;
-            if (!hasReturned_0) {
-                hasReturned_0 = true;
-                retval_0 = 16w12;
-            }
+        hasReturned_0 = false;
+        if (!hasReturned_0) {
+            hasReturned_0 = true;
+            retval_0 = 16w12;
         }
         b = retval_0;
     }
