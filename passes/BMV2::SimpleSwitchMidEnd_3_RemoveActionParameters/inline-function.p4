--- dumps/pruned/inline-function-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:31:50.153991300 +0200
+++ dumps/pruned/inline-function-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:31:50.174076000 +0200
@@ -1,19 +1,25 @@
 control c(inout bit<32> x) {
     bit<32> tmp_3;
+    bit<32> a;
+    bit<32> b;
+    bool hasReturned_1;
+    bit<32> retval_1;
+    bit<32> tmp_4;
+    bit<32> tmp_5;
+    bit<32> a_2;
+    bit<32> b_2;
+    bool hasReturned_2;
+    bit<32> retval_2;
+    bit<32> tmp_6;
     apply {
         {
-            bit<32> a = x;
-            bit<32> b = x;
-            bool hasReturned_1 = false;
-            bit<32> retval_1;
-            bit<32> tmp_4;
-            bit<32> tmp_5;
+            a = x;
+            b = x;
+            hasReturned_1 = false;
             {
-                bit<32> a_2 = a;
-                bit<32> b_2 = b;
-                bool hasReturned_2 = false;
-                bit<32> retval_2;
-                bit<32> tmp_6;
+                a_2 = a;
+                b_2 = b;
+                hasReturned_2 = false;
                 if (a_2 > b_2) 
                     tmp_6 = b_2;
                 else 
