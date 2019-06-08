--- before_pass
+++ after_pass
@@ -30,7 +30,7 @@ control Eg(inout Headers hdrs, inout Met
     @name("Eg.test") action test_0() {
         inKey = { 32w1 };
         defaultKey = { 32w0 };
-        same = inKey == defaultKey;
+        same = true && inKey.field1 == defaultKey.field1;
         val_1 = { 32w0 };
         done = false;
         ok = !done && same;
