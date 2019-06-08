--- before_pass
+++ after_pass
@@ -4,10 +4,7 @@ control c(out bit<16> b) {
     apply {
         {
             hasReturned_0 = false;
-            if (16w10 > 16w12) {
-                hasReturned_0 = true;
-                retval_0 = 16w10;
-            }
+            ;
             if (!hasReturned_0) {
                 hasReturned_0 = true;
                 retval_0 = 16w12;
