--- dumps/pruned/tuple-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:17.524972600 +0200
+++ dumps/pruned/tuple-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:17.528111600 +0200
@@ -9,11 +9,8 @@ struct tuple_0 {
     bool    field_0;
 }
 control c() {
-    tuple_0 x;
     apply {
         {
-            x.field = 32w10;
-            x.field_0 = false;
         }
     }
 }
