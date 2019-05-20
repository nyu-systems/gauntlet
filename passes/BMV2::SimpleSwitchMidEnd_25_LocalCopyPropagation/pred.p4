--- dumps/p4_16_samples/pred.p4/pruned/pred-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:32.689087600 +0200
+++ dumps/p4_16_samples/pred.p4/pruned/pred-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:32.692460400 +0200
@@ -3,9 +3,7 @@
 control empty();
 package top(empty e);
 control Ing() {
-    bool b;
     @name("Ing.cond") action cond_0() {
-        b = true;
     }
     apply {
         cond_0();
