--- dumps/p4_16_samples/tuple0.p4/pruned/tuple0-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:31.183597800 +0200
+++ dumps/p4_16_samples/tuple0.p4/pruned/tuple0-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:31.251360800 +0200
@@ -8,10 +8,8 @@ package top(proto _p);
 control c() {
     tuple_0 x;
     apply {
-        {
-            x.field = 32w10;
-            x.field_0 = false;
-        }
+        x.field = 32w10;
+        x.field_0 = false;
         f(x);
         f({ 32w20, true });
     }
