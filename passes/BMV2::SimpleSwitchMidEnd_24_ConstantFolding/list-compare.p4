--- dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:34:07.925250000 +0200
+++ dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:07.927881500 +0200
@@ -20,8 +20,8 @@ control test(out bool zout) {
             q.l = 32w2;
             q.r = 32w3;
         }
-        zout = true && p.field == 32w4 && p.field_0 == 32w5;
-        zout = zout && (true && q.l == 32w2 && q.r == 32w3);
+        zout = p.field == 32w4 && p.field_0 == 32w5;
+        zout = zout && (q.l == 32w2 && q.r == 32w3);
     }
 }
 top(test()) main;
