--- dumps/pruned/function-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:40.945318100 +0200
+++ dumps/pruned/function-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:31:40.948275700 +0200
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
