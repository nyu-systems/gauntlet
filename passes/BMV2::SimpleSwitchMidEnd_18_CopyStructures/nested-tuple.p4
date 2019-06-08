--- dumps/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-06-08 18:32:59.765040100 +0200
+++ dumps/pruned/nested-tuple-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-06-08 18:32:59.769480800 +0200
@@ -18,7 +18,20 @@ extern void f<T>(in T data);
 control c(inout bit<1> r) {
     S s;
     apply {
-        s = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
+        {
+            {
+                {
+                    s.f1.field_1.f = 1w0;
+                }
+                {
+                    s.f1.field_2.f = 1w1;
+                }
+            }
+            {
+                s.f2.f = 1w0;
+            }
+            s.z = 1w1;
+        }
         f<tuple_1>(s.f1);
         f<tuple_0>({ { 1w0 }, { 1w1 } });
         r = s.f2.f & s.z;
