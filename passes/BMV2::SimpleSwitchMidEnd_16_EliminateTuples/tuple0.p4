--- dumps/pruned/tuple0-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:34:17.712027800 +0200
+++ dumps/pruned/tuple0-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:34:17.714070100 +0200
@@ -1,8 +1,12 @@
-extern void f(in tuple<bit<32>, bool> data);
+struct tuple_0 {
+    bit<32> field;
+    bool    field_0;
+}
+extern void f(in tuple_0 data);
 control proto();
 package top(proto _p);
 control c() {
-    tuple<bit<32>, bool> x;
+    tuple_0 x;
     apply {
         x = { 32w10, false };
         f(x);
