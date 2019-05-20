--- dumps/p4_16_samples/action-bind.p4/pruned/action-bind-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:28:59.368811600 +0200
+++ dumps/p4_16_samples/action-bind.p4/pruned/action-bind-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:28:59.342124000 +0200
@@ -1,12 +1,15 @@
 control c(inout bit<32> x) {
-    @name("c.a") action a_0(inout bit<32> b, bit<32> d) {
+    bit<32> b;
+    @name("c.a") action a_0(bit<32> d) {
+        b = x;
         b = d;
+        x = b;
     }
     @name("c.t") table t {
         actions = {
-            a_0(x);
+            a_0();
         }
-        default_action = a_0(x, 32w0);
+        default_action = a_0(32w0);
     }
     apply {
         t.apply();
