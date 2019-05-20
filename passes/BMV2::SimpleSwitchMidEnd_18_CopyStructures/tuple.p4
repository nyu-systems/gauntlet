--- dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:32:30.760181300 +0200
+++ dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:32:30.763621700 +0200
@@ -11,7 +11,10 @@ struct tuple_0 {
 control c() {
     tuple_0 x;
     apply {
-        x = { 32w10, false };
+        {
+            x.field = 32w10;
+            x.field_0 = false;
+        }
     }
 }
 top(c()) main;
