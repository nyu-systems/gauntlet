--- dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:58.165807700 +0200
+++ dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:32:58.169182300 +0200
@@ -21,8 +21,8 @@ control Eg(inout Headers hdrs, inout Met
         val = res;
         {
             {
-                tmp_0 = (true ? res[31:0] : tmp_0);
-                tmp_0 = (!true ? 32w1 : tmp_0);
+                tmp_0 = res[31:0];
+                tmp_0 = tmp_0;
             }
         }
         val[31:0] = tmp_0;
