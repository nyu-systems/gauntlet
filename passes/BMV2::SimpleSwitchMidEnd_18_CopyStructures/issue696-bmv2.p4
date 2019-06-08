--- dumps/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:39.840050800 +0200
+++ dumps/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:39.843525100 +0200
@@ -56,7 +56,9 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> tmp_1;
     bit<32> tmp_2;
     @name("Eg.test") action test_0() {
-        val = { 32w0 };
+        {
+            val.field1 = 32w0;
+        }
         _pred = val.field1 != 32w0;
         if (_pred) 
             tmp_1 = 32w1;
