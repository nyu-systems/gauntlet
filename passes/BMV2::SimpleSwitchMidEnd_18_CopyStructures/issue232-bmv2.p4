--- before_pass
+++ after_pass
@@ -28,16 +28,26 @@ control Eg(inout Headers hdrs, inout Met
     bool ok;
     Value val_2;
     @name("Eg.test") action test_0() {
-        inKey = { 32w1 };
-        defaultKey = { 32w0 };
+        {
+            inKey.field1 = 32w1;
+        }
+        {
+            defaultKey.field1 = 32w0;
+        }
         same = true && inKey.field1 == defaultKey.field1;
-        val_1 = { 32w0 };
+        {
+            val_1.field1 = 32w0;
+        }
         done = false;
         ok = !done && same;
         if (ok) {
-            val_2 = val_1;
+            {
+                val_2.field1 = val_1.field1;
+            }
             val_2.field1 = 32w8;
-            val_1 = val_2;
+            {
+                val_1.field1 = val_2.field1;
+            }
         }
     }
     apply {
