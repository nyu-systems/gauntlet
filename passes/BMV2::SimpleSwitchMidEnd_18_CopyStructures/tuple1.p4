--- dumps/p4_16_samples/tuple1.p4/pruned/tuple1-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:32:31.458256300 +0200
+++ dumps/p4_16_samples/tuple1.p4/pruned/tuple1-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:32:31.461475600 +0200
@@ -8,7 +8,10 @@ struct tuple_0 {
 control c() {
     tuple_0 x;
     apply {
-        x = { 32w10, false };
+        {
+            x.field = 32w10;
+            x.field_0 = false;
+        }
         f<tuple_0>(x);
     }
 }
