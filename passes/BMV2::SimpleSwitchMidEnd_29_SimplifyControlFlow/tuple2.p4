--- dumps/pruned/tuple2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:18.210669500 +0200
+++ dumps/pruned/tuple2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:18.245091300 +0200
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
