--- before_pass
+++ after_pass
@@ -30,7 +30,7 @@ control Eg(inout Headers hdrs, inout Met
     @name("Eg.test") action test() {
         inKey_0 = { 32w1 };
         defaultKey_0 = { 32w0 };
-        same_0 = inKey_0 == defaultKey_0;
+        same_0 = true && inKey_0.field1 == defaultKey_0.field1;
         val = { 32w0 };
         done_0 = false;
         ok_0 = !done_0 && same_0;
