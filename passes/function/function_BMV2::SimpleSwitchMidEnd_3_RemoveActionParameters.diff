--- before_pass
+++ after_pass
@@ -1,11 +1,14 @@
 control c(out bit<16> b) {
     bit<16> tmp;
+    bit<16> left_0;
+    bit<16> right_0;
+    bool hasReturned;
+    bit<16> retval;
     apply {
         {
-            bit<16> left_0 = 16w10;
-            bit<16> right_0 = 16w12;
-            bool hasReturned = false;
-            bit<16> retval;
+            left_0 = 16w10;
+            right_0 = 16w12;
+            hasReturned = false;
             if (left_0 > right_0) {
                 hasReturned = true;
                 retval = left_0;
