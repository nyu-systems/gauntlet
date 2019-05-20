--- dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:32:30.784304400 +0200
+++ dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:32:30.787624800 +0200
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
