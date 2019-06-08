--- dumps/pruned/inline-action-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:30:57.587812900 +0200
+++ dumps/pruned/inline-action-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:30:57.645494300 +0200
@@ -1,11 +1,7 @@
 control p(inout bit<1> bt) {
     @name("p.b") action b_0() {
-        {
-            bt = bt | 1w1;
-        }
-        {
-            bt = bt | 1w1;
-        }
+        bt = bt | 1w1;
+        bt = bt | 1w1;
     }
     @name("p.t") table t {
         actions = {
