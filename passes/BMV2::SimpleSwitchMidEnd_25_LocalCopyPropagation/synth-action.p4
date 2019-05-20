--- dumps/p4_16_samples/synth-action.p4/pruned/synth-action-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:24.742226800 +0200
+++ dumps/p4_16_samples/synth-action.p4/pruned/synth-action-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:24.746179300 +0200
@@ -1,12 +1,12 @@
 control c(inout bit<32> x) {
     apply {
         x = 32w10;
-        if (x == 32w10) {
-            x = x + 32w2;
-            x = x + 32w4294967290;
+        if (32w10 == 32w10) {
+            x = 32w10 + 32w2;
+            x = 32w10 + 32w2 + 32w4294967290;
         }
         else 
-            x = x << 2;
+            x = 32w10 << 2;
     }
 }
 control n(inout bit<32> x);
