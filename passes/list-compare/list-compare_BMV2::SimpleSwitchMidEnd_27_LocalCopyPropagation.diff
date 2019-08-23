--- before_pass
+++ after_pass
@@ -9,19 +9,9 @@ struct tuple_0 {
     bit<32> field_0;
 }
 control test(out bool zout) {
-    tuple_0 p_0;
-    S q_0;
     apply {
-        {
-            p_0.field = 32w4;
-            p_0.field_0 = 32w5;
-        }
-        {
-            q_0.l = 32w2;
-            q_0.r = 32w3;
-        }
-        zout = p_0.field == 32w4 && p_0.field_0 == 32w5;
-        zout = zout && (q_0.l == 32w2 && q_0.r == 32w3);
+        zout = 32w4 == 32w4 && 32w5 == 32w5;
+        zout = 32w4 == 32w4 && 32w5 == 32w5 && (32w2 == 32w2 && 32w3 == 32w3);
     }
 }
 top(test()) main;
