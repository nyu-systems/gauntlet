--- before_pass
+++ after_pass
@@ -27,6 +27,8 @@ control Eg(inout Headers hdrs, inout Met
     bool done_0;
     bool ok_0;
     Value val_0;
+    bool cond;
+    bool pred;
     @name("Eg.test") action test() {
         {
             inKey_0.field1 = 32w1;
@@ -41,9 +43,7 @@ control Eg(inout Headers hdrs, inout Met
         done_0 = false;
         ok_0 = !done_0 && same_0;
         {
-            bool cond;
             {
-                bool pred;
                 cond = ok_0;
                 pred = cond;
                 {
