--- dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:30:36.932183300 +0200
+++ dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:36.936373400 +0200
@@ -56,7 +56,9 @@ control Eg(inout Headers hdrs, inout Met
     @name("Eg.debug") register<bit<32>>(32w100) debug;
     @name("Eg.reg") register<bit<32>>(32w1) reg;
     @name("Eg.test") action test_0() {
-        val = { 32w0 };
+        {
+            val.field1 = 32w0;
+        }
         _pred = val.field1 != 32w0;
         if (_pred) 
             tmp_1 = 32w1;
