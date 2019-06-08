--- dumps/pruned/tuple1-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:17.984946500 +0200
+++ dumps/pruned/tuple1-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:18.020537300 +0200
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
