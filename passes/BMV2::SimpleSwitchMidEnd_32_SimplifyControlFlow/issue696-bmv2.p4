--- before_pass
+++ after_pass
@@ -53,18 +53,10 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> tmp;
     bit<32> tmp_0;
     @name("Eg.test") action test() {
-        {
-            {
-                tmp = tmp;
-                tmp = 32w0;
-            }
-        }
-        {
-            {
-                tmp_0 = tmp_0;
-                tmp_0 = 32w0;
-            }
-        }
+        tmp = tmp;
+        tmp = 32w0;
+        tmp_0 = tmp_0;
+        tmp_0 = 32w0;
         debug.write(32w0, tmp_0);
         debug.write(32w1, tmp);
         debug.write(32w2, tmp);
