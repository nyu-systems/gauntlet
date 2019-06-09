--- before_pass
+++ after_pass
@@ -12,8 +12,14 @@ control test(out bool zout) {
     tuple_0 p_0;
     S q_0;
     apply {
-        p_0 = { 32w4, 32w5 };
-        q_0 = { 32w2, 32w3 };
+        {
+            p_0.field = 32w4;
+            p_0.field_0 = 32w5;
+        }
+        {
+            q_0.l = 32w2;
+            q_0.r = 32w3;
+        }
         zout = true && p_0.field == 32w4 && p_0.field_0 == 32w5;
         zout = zout && (true && q_0.l == {32w2,32w3}.l && q_0.r == {32w2,32w3}.r);
     }
