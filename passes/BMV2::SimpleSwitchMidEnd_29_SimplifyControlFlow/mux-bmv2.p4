--- before_pass
+++ after_pass
@@ -19,12 +19,8 @@ control Eg(inout Headers hdrs, inout Met
     bit<64> val;
     @name("Eg.update") action update_0() {
         val = res;
-        {
-            {
-                tmp_0 = res[31:0];
-                tmp_0 = tmp_0;
-            }
-        }
+        tmp_0 = res[31:0];
+        tmp_0 = tmp_0;
         val[31:0] = tmp_0;
         res = val;
     }
