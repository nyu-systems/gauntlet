--- dumps/p4_16_samples/action_param1.p4/pruned/action_param1-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:29:01.478014200 +0200
+++ dumps/p4_16_samples/action_param1.p4/pruned/action_param1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:29:01.497216800 +0200
@@ -1,9 +1,11 @@
 control c(inout bit<32> x) {
-    @name("c.a") action a_0(in bit<32> arg_1) {
+    bit<32> arg_1;
+    @name("c.a") action a_0() {
+        arg_1 = 32w15;
         x = arg_1;
     }
     apply {
-        a_0(32w15);
+        a_0();
     }
 }
 control proto(inout bit<32> arg);
