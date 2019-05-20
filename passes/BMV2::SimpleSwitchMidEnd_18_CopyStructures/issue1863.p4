--- dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:30:33.765881300 +0200
+++ dumps/p4_16_samples/issue1863.p4/pruned/issue1863-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:30:33.768438200 +0200
@@ -5,8 +5,14 @@ struct S {
 control c(out bit<1> b) {
     S s;
     apply {
-        s = { 1w0, 1w1 };
-        s = { s.b, s.a };
+        {
+            s.a = 1w0;
+            s.b = 1w1;
+        }
+        {
+            s.a = s.b;
+            s.b = s.a;
+        }
         b = s.a;
     }
 }
