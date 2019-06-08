--- before_pass
+++ after_pass
@@ -55,22 +55,12 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> tmp_1;
     bit<32> tmp_2;
     @name("Eg.test") action test_0() {
-        {
-            val.field1 = 32w0;
-        }
-        {
-            {
-                tmp_1 = tmp_1;
-                tmp_1 = 32w0;
-            }
-        }
+        val.field1 = 32w0;
+        tmp_1 = tmp_1;
+        tmp_1 = 32w0;
         inc = tmp_1;
-        {
-            {
-                tmp_2 = tmp_2;
-                tmp_2 = 32w0;
-            }
-        }
+        tmp_2 = tmp_2;
+        tmp_2 = 32w0;
         debug.write(32w0, tmp_2);
         debug.write(32w1, inc);
         val.field1 = 32w1;
