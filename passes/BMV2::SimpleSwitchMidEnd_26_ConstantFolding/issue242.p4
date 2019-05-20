--- dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:36.988084800 +0200
+++ dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:30:36.992359900 +0200
@@ -60,15 +60,15 @@ control Eg(inout Headers hdrs, inout Met
         }
         {
             {
-                tmp_1 = (32w0 != 32w0 ? 32w1 : tmp_1);
-                tmp_1 = (!(32w0 != 32w0) ? 32w0 : tmp_1);
+                tmp_1 = tmp_1;
+                tmp_1 = 32w0;
             }
         }
         inc = tmp_1;
         {
             {
-                tmp_2 = (32w0 != 32w0 ? 32w1 : tmp_2);
-                tmp_2 = (!(32w0 != 32w0) ? 32w0 : tmp_2);
+                tmp_2 = tmp_2;
+                tmp_2 = 32w0;
             }
         }
         debug.write(32w0, tmp_2);
