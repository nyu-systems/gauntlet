--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:19.145183600 +0200
+++ dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:19.148592300 +0200
@@ -9,19 +9,13 @@ struct tuple_0 {
     bit<32> field_0;
 }
 control test(out bool zout) {
-    tuple_0 p;
-    S q;
     apply {
         {
-            p.field = 32w4;
-            p.field_0 = 32w5;
         }
         {
-            q.l = 32w2;
-            q.r = 32w3;
         }
-        zout = p.field == 32w4 && p.field_0 == 32w5;
-        zout = zout && (q.l == 32w2 && q.r == 32w3);
+        zout = 32w4 == 32w4 && 32w5 == 32w5;
+        zout = 32w4 == 32w4 && 32w5 == 32w5 && (32w2 == 32w2 && 32w3 == 32w3);
     }
 }
 top(test()) main;
