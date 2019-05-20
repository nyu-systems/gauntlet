--- dumps/p4_16_samples/pred1.p4/pruned/pred1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:31:33.122891700 +0200
+++ dumps/p4_16_samples/pred1.p4/pruned/pred1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:31:33.125367600 +0200
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
