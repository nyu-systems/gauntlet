--- dumps/p4_16_samples/direct-action.p4/pruned/direct-action-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:34.565987400 +0200
+++ dumps/p4_16_samples/direct-action.p4/pruned/direct-action-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:34.571244900 +0200
@@ -1,9 +1,7 @@
 control c(inout bit<16> y) {
     bit<32> x;
-    bit<32> arg;
     @name("c.a") action a_0() {
-        arg = x;
-        y = (bit<16>)arg;
+        y = (bit<16>)x;
     }
     apply {
         x = 32w2;
