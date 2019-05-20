--- dumps/p4_16_samples/action-bind.p4/pruned/action-bind-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:28:59.302444900 +0200
+++ dumps/p4_16_samples/action-bind.p4/pruned/action-bind-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:28:59.304693000 +0200
@@ -1,9 +1,6 @@
 control c(inout bit<32> x) {
-    bit<32> b;
     @name("c.a") action a_0(bit<32> d) {
-        b = x;
-        b = d;
-        x = b;
+        x = d;
     }
     @name("c.t") table t {
         actions = {
