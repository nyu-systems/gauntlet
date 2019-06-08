--- dumps/pruned/direct-action1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:31.802425200 +0200
+++ dumps/pruned/direct-action1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:31.805009400 +0200
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
         x = 32w10;
