--- before_pass
+++ after_pass
@@ -4,10 +4,7 @@ control c(out bit<16> b) {
     apply {
         {
             hasReturned = false;
-            if (16w10 > 16w12) {
-                hasReturned = true;
-                retval = 16w10;
-            }
+            ;
             if (!hasReturned) {
                 hasReturned = true;
                 retval = 16w12;
