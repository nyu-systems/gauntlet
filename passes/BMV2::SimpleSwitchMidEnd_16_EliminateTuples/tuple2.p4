--- dumps/p4_16_samples/tuple2.p4/pruned/tuple2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:32:31.832656700 +0200
+++ dumps/p4_16_samples/tuple2.p4/pruned/tuple2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:32:31.840342300 +0200
@@ -1,11 +1,15 @@
 extern void f<T>(in T data);
 control proto();
 package top(proto _p);
+struct tuple_0 {
+    bit<32> field;
+    bool    field_0;
+}
 control c() {
-    tuple<bit<32>, bool> x_0;
+    tuple_0 x_0;
     apply {
         x_0 = { 32w10, false };
-        f<tuple<bit<32>, bool>>(x_0);
+        f<tuple_0>(x_0);
     }
 }
 top(c()) main;
