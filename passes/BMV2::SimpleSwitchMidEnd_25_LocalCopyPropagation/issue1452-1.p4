--- dumps/pruned/issue1452-1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:01.614155500 +0200
+++ dumps/pruned/issue1452-1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:01.616733200 +0200
@@ -1,9 +1,5 @@
 control c() {
-    bit<32> x;
-    bit<32> arg;
     @name("c.b") action b_0() {
-        arg = 32w2;
-        x = arg;
     }
     apply {
         b_0();
