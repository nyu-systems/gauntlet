--- dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:32:18.012483900 +0200
+++ dumps/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:18.016278600 +0200
@@ -30,7 +30,7 @@ control Eg(inout Headers hdrs, inout Met
     @name("Eg.test") action test_0() {
         inKey = { 32w1 };
         defaultKey = { 32w0 };
-        same = inKey == defaultKey;
+        same = true && inKey.field1 == defaultKey.field1;
         val_1 = { 32w0 };
         done = false;
         ok = !done && same;
