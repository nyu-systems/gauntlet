--- dumps/pruned/action-bind-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:30:58.620338400 +0200
+++ dumps/pruned/action-bind-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:30:58.622599300 +0200
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
