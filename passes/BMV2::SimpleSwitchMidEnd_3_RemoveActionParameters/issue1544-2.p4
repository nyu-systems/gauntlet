--- dumps/pruned/issue1544-2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:04.969044800 +0200
+++ dumps/pruned/issue1544-2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:04.936214000 +0200
@@ -4,13 +4,20 @@ control c(inout bit<32> x) {
     bit<32> tmp_7;
     bit<32> tmp_8;
     bit<32> tmp_9;
+    bit<32> a;
+    bit<32> b;
+    bool hasReturned_0;
+    bit<32> retval_0;
+    bit<32> tmp_10;
+    bit<32> a_3;
+    bit<32> b_3;
+    bit<32> a_4;
+    bit<32> b_4;
     apply {
         {
-            bit<32> a = x;
-            bit<32> b = x + 32w1;
-            bool hasReturned_0 = false;
-            bit<32> retval_0;
-            bit<32> tmp_10;
+            a = x;
+            b = x + 32w1;
+            hasReturned_0 = false;
             if (a > b) 
                 tmp_10 = b;
             else 
@@ -21,11 +28,9 @@ control c(inout bit<32> x) {
         }
         tmp_6 = tmp_5;
         {
-            bit<32> a_3 = x;
-            bit<32> b_3 = x + 32w4294967295;
-            bool hasReturned_0 = false;
-            bit<32> retval_0;
-            bit<32> tmp_10;
+            a_3 = x;
+            b_3 = x + 32w4294967295;
+            hasReturned_0 = false;
             if (a_3 > b_3) 
                 tmp_10 = b_3;
             else 
@@ -36,11 +41,9 @@ control c(inout bit<32> x) {
         }
         tmp_8 = tmp_7;
         {
-            bit<32> a_4 = tmp_6;
-            bit<32> b_4 = tmp_8;
-            bool hasReturned_0 = false;
-            bit<32> retval_0;
-            bit<32> tmp_10;
+            a_4 = tmp_6;
+            b_4 = tmp_8;
+            hasReturned_0 = false;
             if (a_4 > b_4) 
                 tmp_10 = b_4;
             else 
