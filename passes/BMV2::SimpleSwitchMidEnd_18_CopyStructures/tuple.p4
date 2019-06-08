--- dumps/pruned/tuple-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:34:17.498253900 +0200
+++ dumps/pruned/tuple-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:34:17.500540500 +0200
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
