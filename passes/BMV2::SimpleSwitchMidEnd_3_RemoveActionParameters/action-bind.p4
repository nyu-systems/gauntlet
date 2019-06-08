--- dumps/pruned/action-bind-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:30:58.678844100 +0200
+++ dumps/pruned/action-bind-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:30:58.657178900 +0200
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
