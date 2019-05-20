--- dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:02.998426200 +0200
+++ dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:31:03.002252200 +0200
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
