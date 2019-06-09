--- before_pass
+++ after_pass
@@ -28,16 +28,26 @@ control Eg(inout Headers hdrs, inout Met
     bool ok_0;
     Value val_0;
     @name("Eg.test") action test() {
-        inKey_0 = { 32w1 };
-        defaultKey_0 = { 32w0 };
+        {
+            inKey_0.field1 = 32w1;
+        }
+        {
+            defaultKey_0.field1 = 32w0;
+        }
         same_0 = true && inKey_0.field1 == defaultKey_0.field1;
-        val = { 32w0 };
+        {
+            val.field1 = 32w0;
+        }
         done_0 = false;
         ok_0 = !done_0 && same_0;
         if (ok_0) {
-            val_0 = val;
+            {
+                val_0.field1 = val.field1;
+            }
             val_0.field1 = 32w8;
-            val = val_0;
+            {
+                val.field1 = val_0.field1;
+            }
         }
     }
     apply {
