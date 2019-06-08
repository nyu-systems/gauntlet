--- dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:07.927881500 +0200
+++ dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:07.930321900 +0200
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
