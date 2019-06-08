--- before_pass
+++ after_pass
@@ -60,15 +60,15 @@ control Eg(inout Headers hdrs, inout Met
         }
         {
             {
-                tmp_1 = (32w0 != 32w0 ? 32w1 : tmp_1);
-                tmp_1 = (!(32w0 != 32w0) ? 32w0 : tmp_1);
+                tmp_1 = tmp_1;
+                tmp_1 = 32w0;
             }
         }
         inc = tmp_1;
         {
             {
-                tmp_2 = (32w0 != 32w0 ? 32w1 : tmp_2);
-                tmp_2 = (!(32w0 != 32w0) ? 32w0 : tmp_2);
+                tmp_2 = tmp_2;
+                tmp_2 = 32w0;
             }
         }
         debug.write(32w0, tmp_2);
