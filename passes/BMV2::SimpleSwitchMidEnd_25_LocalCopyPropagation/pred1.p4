--- dumps/pruned/pred1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:33:06.762620400 +0200
+++ dumps/pruned/pred1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:06.767163500 +0200
@@ -3,13 +3,9 @@
 control empty();
 package top(empty e);
 control Ing() {
-    bool b;
-    bit<32> a;
     @name("Ing.cond") action cond_0() {
-        b = true;
     }
     apply {
-        a = 32w2;
         cond_0();
     }
 }
