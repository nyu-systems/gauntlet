--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:30:36.375143400 +0200
+++ dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:30:36.399847900 +0200
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
