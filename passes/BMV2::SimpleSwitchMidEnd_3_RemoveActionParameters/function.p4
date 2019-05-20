--- dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:29:48.328933700 +0200
+++ dumps/p4_16_samples/function.p4/pruned/function-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:29:48.355611200 +0200
@@ -1,11 +1,14 @@
 control c(out bit<16> b) {
     bit<16> tmp_0;
+    bit<16> left;
+    bit<16> right;
+    bool hasReturned_0;
+    bit<16> retval_0;
     apply {
         {
-            bit<16> left = 16w10;
-            bit<16> right = 16w12;
-            bool hasReturned_0 = false;
-            bit<16> retval_0;
+            left = 16w10;
+            right = 16w12;
+            hasReturned_0 = false;
             if (left > right) {
                 hasReturned_0 = true;
                 retval_0 = left;
