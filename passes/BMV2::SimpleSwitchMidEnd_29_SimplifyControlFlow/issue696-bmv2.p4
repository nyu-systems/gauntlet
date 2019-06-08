--- dumps/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:39.880411100 +0200
+++ dumps/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:39.950653900 +0200
@@ -55,22 +55,12 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> tmp_1;
     bit<32> tmp_2;
     @name("Eg.test") action test_0() {
-        {
-            val.field1 = 32w0;
-        }
-        {
-            {
-                tmp_1 = tmp_1;
-                tmp_1 = 32w0;
-            }
-        }
+        val.field1 = 32w0;
+        tmp_1 = tmp_1;
+        tmp_1 = 32w0;
         inc = tmp_1;
-        {
-            {
-                tmp_2 = tmp_2;
-                tmp_2 = 32w0;
-            }
-        }
+        tmp_2 = tmp_2;
+        tmp_2 = 32w0;
         debug.write(32w0, tmp_2);
         debug.write(32w1, inc);
         val.field1 = 32w1;
