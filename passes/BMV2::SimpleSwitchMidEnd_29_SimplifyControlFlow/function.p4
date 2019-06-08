--- dumps/pruned/function-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:40.958109000 +0200
+++ dumps/pruned/function-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:41.020027700 +0200
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
