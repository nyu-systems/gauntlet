--- before_pass
+++ after_pass
@@ -53,18 +53,10 @@ control Eg(inout Headers hdrs, inout Met
     @name("Eg.debug") register<bit<32>>(32w100) debug_0;
     @name("Eg.reg") register<bit<32>>(32w1) reg_0;
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
         debug_0.write(32w0, tmp_0);
         debug_0.write(32w1, tmp);
         debug_0.write(32w2, tmp);
