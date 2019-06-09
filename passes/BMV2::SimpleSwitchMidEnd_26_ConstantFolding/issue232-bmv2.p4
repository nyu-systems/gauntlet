--- before_pass
+++ after_pass
@@ -36,7 +36,7 @@ control Eg(inout Headers hdrs, inout Met
         {
             defaultKey_0.field1 = 32w0;
         }
-        same_0 = true && inKey_0.field1 == defaultKey_0.field1;
+        same_0 = inKey_0.field1 == defaultKey_0.field1;
         {
             val.field1 = 32w0;
         }
