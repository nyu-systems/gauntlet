--- dumps/p4_16_samples/action_param.p4/pruned/action_param-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:01.212877200 +0200
+++ dumps/p4_16_samples/action_param.p4/pruned/action_param-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:01.216370600 +0200
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
