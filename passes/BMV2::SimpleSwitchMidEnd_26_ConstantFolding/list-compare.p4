--- before_pass
+++ after_pass
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
