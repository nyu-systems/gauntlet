--- dumps/pruned/function-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:31:40.960940800 +0200
+++ dumps/pruned/function-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:31:40.990218200 +0200
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
