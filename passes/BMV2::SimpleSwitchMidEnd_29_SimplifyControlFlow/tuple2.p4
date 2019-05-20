--- dumps/p4_16_samples/tuple2.p4/pruned/tuple2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:32:31.895116100 +0200
+++ dumps/p4_16_samples/tuple2.p4/pruned/tuple2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:32:31.967665700 +0200
@@ -8,10 +8,8 @@ struct tuple_0 {
 control c() {
     tuple_0 x_0;
     apply {
-        {
-            x_0.field = 32w10;
-            x_0.field_0 = false;
-        }
+        x_0.field = 32w10;
+        x_0.field_0 = false;
         f<tuple_0>(x_0);
     }
 }
