--- dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:18.016278600 +0200
+++ dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:18.020179500 +0200
@@ -28,16 +28,26 @@ control Eg(inout Headers hdrs, inout Met
     bool ok;
     Value val_2;
     @name("Eg.test") action test_0() {
-        inKey = { 32w1 };
-        defaultKey = { 32w0 };
+        {
+            inKey.field1 = 32w1;
+        }
+        {
+            defaultKey.field1 = 32w0;
+        }
         same = true && inKey.field1 == defaultKey.field1;
-        val_1 = { 32w0 };
+        {
+            val_1.field1 = 32w0;
+        }
         done = false;
         ok = !done && same;
         if (ok) {
-            val_2 = val_1;
+            {
+                val_2.field1 = val_1.field1;
+            }
             val_2.field1 = 32w8;
-            val_1 = val_2;
+            {
+                val_1.field1 = val_2.field1;
+            }
         }
     }
     apply {
