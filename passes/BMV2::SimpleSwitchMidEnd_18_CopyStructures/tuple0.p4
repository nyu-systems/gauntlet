--- dumps/pruned/tuple0-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:34:17.716039800 +0200
+++ dumps/pruned/tuple0-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:34:17.720017600 +0200
@@ -8,7 +8,10 @@ package top(proto _p);
 control c() {
     tuple_0 x;
     apply {
-        x = { 32w10, false };
+        {
+            x.field = 32w10;
+            x.field_0 = false;
+        }
         f(x);
         f({ 32w20, true });
     }
