--- dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:48.309898400 +0200
+++ dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:29:48.312751000 +0200
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
