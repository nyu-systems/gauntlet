--- dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:07.930321900 +0200
+++ dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:34:07.932335500 +0200
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
