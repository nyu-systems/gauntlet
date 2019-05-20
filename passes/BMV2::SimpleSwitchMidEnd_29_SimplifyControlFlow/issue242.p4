--- dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:30:36.999867700 +0200
+++ dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:30:37.061410700 +0200
@@ -55,22 +55,12 @@ control Eg(inout Headers hdrs, inout Met
     @name("Eg.debug") register<bit<32>>(32w100) debug;
     @name("Eg.reg") register<bit<32>>(32w1) reg;
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
