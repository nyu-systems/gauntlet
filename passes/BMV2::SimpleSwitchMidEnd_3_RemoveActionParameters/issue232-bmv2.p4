--- before_pass
+++ after_pass
@@ -26,6 +26,7 @@ control Eg(inout Headers hdrs, inout Met
     Value val_1;
     bool done;
     bool ok;
+    Value val_2;
     @name("Eg.test") action test_0() {
         inKey = { 32w1 };
         defaultKey = { 32w0 };
@@ -34,7 +35,7 @@ control Eg(inout Headers hdrs, inout Met
         done = false;
         ok = !done && same;
         if (ok) {
-            Value val_2 = val_1;
+            val_2 = val_1;
             val_2.field1 = 32w8;
             val_1 = val_2;
         }
