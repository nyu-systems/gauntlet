--- before_pass
+++ after_pass
@@ -26,6 +26,7 @@ control Eg(inout Headers hdrs, inout Met
     Value val;
     bool done_0;
     bool ok_0;
+    Value val_0;
     @name("Eg.test") action test() {
         inKey_0 = { 32w1 };
         defaultKey_0 = { 32w0 };
@@ -34,7 +35,7 @@ control Eg(inout Headers hdrs, inout Met
         done_0 = false;
         ok_0 = !done_0 && same_0;
         if (ok_0) {
-            Value val_0 = val;
+            val_0 = val;
             val_0.field1 = 32w8;
             val = val_0;
         }
