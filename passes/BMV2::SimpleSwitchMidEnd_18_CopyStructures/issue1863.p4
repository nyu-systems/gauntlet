--- dumps/pruned/issue1863-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:15.964389200 +0200
+++ dumps/pruned/issue1863-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:15.966630800 +0200
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
