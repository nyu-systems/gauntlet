--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:24.644810000 +0200
+++ dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:31:24.649854500 +0200
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
