--- before_pass
+++ after_pass
@@ -27,6 +27,8 @@ control Eg(inout Headers hdrs, inout Met
     bool done;
     bool ok;
     Value val_2;
+    bool cond;
+    bool pred;
     @name("Eg.test") action test_0() {
         {
             inKey.field1 = 32w1;
@@ -41,9 +43,7 @@ control Eg(inout Headers hdrs, inout Met
         done = false;
         ok = !done && same;
         {
-            bool cond;
             {
-                bool pred;
                 cond = ok;
                 pred = cond;
                 {
