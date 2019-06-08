--- dumps/pruned/action_param-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:01.032996100 +0200
+++ dumps/pruned/action_param-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:31:01.035398900 +0200
@@ -1,8 +1,6 @@
 control c(inout bit<32> x) {
-    bit<32> arg_1;
     @name("c.a") action a_0() {
-        arg_1 = 32w10;
-        x = arg_1;
+        x = 32w10;
     }
     @name("c.t") table t {
         actions = {
