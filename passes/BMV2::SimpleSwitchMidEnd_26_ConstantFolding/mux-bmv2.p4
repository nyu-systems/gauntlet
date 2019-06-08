--- before_pass
+++ after_pass
@@ -21,8 +21,8 @@ control Eg(inout Headers hdrs, inout Met
         val = res;
         {
             {
-                tmp_0 = (true ? res[31:0] : tmp_0);
-                tmp_0 = (!true ? 32w1 : tmp_0);
+                tmp_0 = res[31:0];
+                tmp_0 = tmp_0;
             }
         }
         val[31:0] = tmp_0;
