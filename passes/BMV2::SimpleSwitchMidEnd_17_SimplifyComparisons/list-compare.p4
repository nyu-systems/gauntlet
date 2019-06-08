--- dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:34:07.904435900 +0200
+++ dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:34:07.906651100 +0200
@@ -14,8 +14,8 @@ control test(out bool zout) {
     apply {
         p = { 32w4, 32w5 };
         q = { 32w2, 32w3 };
-        zout = p == { 32w4, 32w5 };
-        zout = zout && q == { 32w2, 32w3 };
+        zout = true && p.field == 32w4 && p.field_0 == 32w5;
+        zout = zout && (true && q.l == 32w2 && q.r == 32w3);
     }
 }
 top(test()) main;
