--- dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:29:48.325912400 +0200
+++ dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:29:48.391728900 +0200
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
