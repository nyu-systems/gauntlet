--- dumps/pruned/issue242-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:18.701900300 +0200
+++ dumps/pruned/issue242-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:32:18.703936900 +0200
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
