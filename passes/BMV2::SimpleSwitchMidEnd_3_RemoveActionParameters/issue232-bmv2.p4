--- dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:18.061836700 +0200
+++ dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:18.092653500 +0200
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
