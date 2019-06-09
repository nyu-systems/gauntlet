--- before_pass
+++ after_pass
@@ -55,14 +55,14 @@ control Eg(inout Headers hdrs, inout Met
     @name("Eg.test") action test() {
         {
             {
-                tmp = (32w0 != 32w0 ? 32w1 : tmp);
-                tmp = (!(32w0 != 32w0) ? 32w0 : tmp);
+                tmp = tmp;
+                tmp = 32w0;
             }
         }
         {
             {
-                tmp_0 = (32w0 != 32w0 ? 32w1 : tmp_0);
-                tmp_0 = (!(32w0 != 32w0) ? 32w0 : tmp_0);
+                tmp_0 = tmp_0;
+                tmp_0 = 32w0;
             }
         }
         debug_0.write(32w0, tmp_0);
