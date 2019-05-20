--- dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:31:26.442460100 +0200
+++ dumps/p4_16_samples/nested-tuple1.p4/pruned/nested-tuple1-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:31:26.446465400 +0200
@@ -1,10 +1,14 @@
 struct T {
     bit<1> f;
 }
+struct tuple_0 {
+    T field;
+    T field_0;
+}
 struct S {
-    tuple<T, T> f1;
-    T           f2;
-    bit<1>      z;
+    tuple_0 f1;
+    T       f2;
+    bit<1>  z;
 }
 extern void f<D>(in D data);
 control c(inout bit<1> r) {
@@ -12,7 +16,7 @@ control c(inout bit<1> r) {
     bit<1> tmp;
     apply {
         s_0 = { { { 1w0 }, { 1w1 } }, { 1w0 }, 1w1 };
-        f<tuple<T, T>>(s_0.f1);
+        f<tuple_0>(s_0.f1);
         tmp = s_0.f2.f & s_0.z;
         r = tmp;
     }
