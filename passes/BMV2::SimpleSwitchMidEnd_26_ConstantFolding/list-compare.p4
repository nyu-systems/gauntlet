--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:19.148592300 +0200
+++ dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 17:32:19.151649000 +0200
@@ -14,8 +14,8 @@ control test(out bool zout) {
         }
         {
         }
-        zout = 32w4 == 32w4 && 32w5 == 32w5;
-        zout = 32w4 == 32w4 && 32w5 == 32w5 && (32w2 == 32w2 && 32w3 == 32w3);
+        zout = true;
+        zout = true;
     }
 }
 top(test()) main;
