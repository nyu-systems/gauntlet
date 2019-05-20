--- dumps/p4_16_samples/tuple1.p4/pruned/tuple1-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:31.501242100 +0200
+++ dumps/p4_16_samples/tuple1.p4/pruned/tuple1-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:31.568995300 +0200
@@ -8,10 +8,8 @@ struct tuple_0 {
 control c() {
     tuple_0 x;
     apply {
-        {
-            x.field = 32w10;
-            x.field_0 = false;
-        }
+        x.field = 32w10;
+        x.field_0 = false;
         f<tuple_0>(x);
     }
 }
