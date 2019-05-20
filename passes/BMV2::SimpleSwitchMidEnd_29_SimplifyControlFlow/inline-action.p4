--- dumps/p4_16_samples/inline-action.p4/pruned/inline-action-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:28:58.713224800 +0200
+++ dumps/p4_16_samples/inline-action.p4/pruned/inline-action-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:28:58.765427200 +0200
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
