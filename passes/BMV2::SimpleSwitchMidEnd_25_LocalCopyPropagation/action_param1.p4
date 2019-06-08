--- dumps/pruned/action_param1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:01.315604500 +0200
+++ dumps/pruned/action_param1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:01.319669400 +0200
@@ -1,8 +1,6 @@
 control c(inout bit<32> x) {
-    bit<32> arg_1;
     @name("c.a") action a_0() {
-        arg_1 = 32w15;
-        x = arg_1;
+        x = 32w15;
     }
     apply {
         a_0();
