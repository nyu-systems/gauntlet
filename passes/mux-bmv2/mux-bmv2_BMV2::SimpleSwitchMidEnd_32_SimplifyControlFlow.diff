--- before_pass
+++ after_pass
@@ -19,12 +19,8 @@ control Eg(inout Headers hdrs, inout Met
     bit<64> val;
     @name("Eg.update") action update() {
         val = res_0;
-        {
-            {
-                tmp = res_0[31:0];
-                tmp = tmp;
-            }
-        }
+        tmp = res_0[31:0];
+        tmp = tmp;
         val[31:0] = tmp;
         res_0 = val;
     }
