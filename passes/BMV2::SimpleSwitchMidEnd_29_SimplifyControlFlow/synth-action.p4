--- dumps/pruned/synth-action-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:12.541489100 +0200
+++ dumps/pruned/synth-action-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:12.608832900 +0200
@@ -1,10 +1,8 @@
 control c(inout bit<32> x) {
     apply {
         x = 32w10;
-        {
-            x = 32w12;
-            x = 32w6;
-        }
+        x = 32w12;
+        x = 32w6;
     }
 }
 control n(inout bit<32> x);
