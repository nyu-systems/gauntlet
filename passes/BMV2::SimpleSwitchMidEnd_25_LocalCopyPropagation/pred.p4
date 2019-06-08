--- dumps/pruned/pred-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:33:06.464974900 +0200
+++ dumps/pruned/pred-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:06.466959200 +0200
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
