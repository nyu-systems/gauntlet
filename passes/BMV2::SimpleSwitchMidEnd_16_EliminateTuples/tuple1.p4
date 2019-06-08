--- dumps/pruned/tuple1-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:34:17.946620400 +0200
+++ dumps/pruned/tuple1-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:34:17.948816400 +0200
@@ -1,11 +1,15 @@
 extern void f<T>(in T data);
 control proto();
 package top(proto _p);
+struct tuple_0 {
+    bit<32> field;
+    bool    field_0;
+}
 control c() {
-    tuple<bit<32>, bool> x;
+    tuple_0 x;
     apply {
         x = { 32w10, false };
-        f<tuple<bit<32>, bool>>(x);
+        f<tuple_0>(x);
     }
 }
 top(c()) main;
