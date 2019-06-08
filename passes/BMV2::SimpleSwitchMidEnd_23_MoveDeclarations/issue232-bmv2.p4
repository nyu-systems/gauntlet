--- dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:18.035043700 +0200
+++ dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:18.038766200 +0200
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
