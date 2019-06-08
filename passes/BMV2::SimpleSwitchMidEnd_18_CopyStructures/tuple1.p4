--- dumps/pruned/tuple1-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:34:17.951003300 +0200
+++ dumps/pruned/tuple1-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:34:17.954270700 +0200
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
