--- before_pass
+++ after_pass
@@ -12,8 +12,14 @@ control test(out bool zout) {
     tuple_0 p;
     S q;
     apply {
-        p = { 32w4, 32w5 };
-        q = { 32w2, 32w3 };
+        {
+            p.field = 32w4;
+            p.field_0 = 32w5;
+        }
+        {
+            q.l = 32w2;
+            q.r = 32w3;
+        }
         zout = true && p.field == 32w4 && p.field_0 == 32w5;
         zout = zout && (true && q.l == 32w2 && q.r == 32w3);
     }
