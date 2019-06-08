--- dumps/pruned/synth-action-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:12.529927100 +0200
+++ dumps/pruned/synth-action-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-06-08 18:34:12.533862700 +0200
@@ -1,12 +1,10 @@
 control c(inout bit<32> x) {
     apply {
         x = 32w10;
-        if (32w10 == 32w10) {
-            x = 32w10 + 32w2;
-            x = 32w10 + 32w2 + 32w4294967290;
+        {
+            x = 32w12;
+            x = 32w6;
         }
-        else 
-            x = 32w10 << 2;
     }
 }
 control n(inout bit<32> x);
