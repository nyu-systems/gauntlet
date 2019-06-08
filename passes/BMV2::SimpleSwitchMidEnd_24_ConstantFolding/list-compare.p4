--- before_pass
+++ after_pass
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
