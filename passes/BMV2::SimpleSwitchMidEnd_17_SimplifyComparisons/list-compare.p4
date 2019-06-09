--- before_pass
+++ after_pass
@@ -14,8 +14,8 @@ control test(out bool zout) {
     apply {
         p_0 = { 32w4, 32w5 };
         q_0 = { 32w2, 32w3 };
-        zout = p_0 == { 32w4, 32w5 };
-        zout = zout && q_0 == {32w2,32w3};
+        zout = true && p_0.field == 32w4 && p_0.field_0 == 32w5;
+        zout = zout && (true && q_0.l == {32w2,32w3}.l && q_0.r == {32w2,32w3}.r);
     }
 }
 top(test()) main;
