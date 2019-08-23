--- before_pass
+++ after_pass
@@ -21,8 +21,8 @@ control Eg(inout Headers hdrs, inout Met
         val = res_0;
         {
             {
-                tmp = (true ? res_0[31:0] : tmp);
-                tmp = (!true ? 32w1 : tmp);
+                tmp = res_0[31:0];
+                tmp = tmp;
             }
         }
         val[31:0] = tmp;
