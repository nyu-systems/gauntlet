--- dumps/p4_16_samples/action_param1.p4/pruned/action_param1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:29:01.465131500 +0200
+++ dumps/p4_16_samples/action_param1.p4/pruned/action_param1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:29:01.467004100 +0200
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
