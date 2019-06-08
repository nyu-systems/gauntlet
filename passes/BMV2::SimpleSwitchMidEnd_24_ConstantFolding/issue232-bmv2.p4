--- before_pass
+++ after_pass
@@ -36,7 +36,7 @@ control Eg(inout Headers hdrs, inout Met
         {
             defaultKey.field1 = 32w0;
         }
-        same = true && inKey.field1 == defaultKey.field1;
+        same = inKey.field1 == defaultKey.field1;
         {
             val_1.field1 = 32w0;
         }
