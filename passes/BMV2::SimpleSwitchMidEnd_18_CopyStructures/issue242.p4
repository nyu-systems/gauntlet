--- dumps/pruned/issue242-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:18.684540800 +0200
+++ dumps/pruned/issue242-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:18.686671400 +0200
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
