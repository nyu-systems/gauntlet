--- dumps/p4_16_samples/issue1452.p4/pruned/issue1452-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:30:16.326381600 +0200
+++ dumps/p4_16_samples/issue1452.p4/pruned/issue1452-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:30:16.328846900 +0200
@@ -1,13 +1,7 @@
 control c() {
     bit<32> x;
-    bool hasReturned_0;
-    bit<32> arg;
     @name("c.a") action a_0() {
-        arg = x;
-        hasReturned_0 = false;
-        arg = 32w1;
-        hasReturned_0 = true;
-        x = arg;
+        x = 32w1;
     }
     apply {
         a_0();
