--- dumps/pruned/issue1452-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:01.888202800 +0200
+++ dumps/pruned/issue1452-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:01.890966300 +0200
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
