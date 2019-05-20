--- dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:32:19.096152000 +0200
+++ dumps/p4_16_samples/list-compare.p4/pruned/list-compare-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:32:19.100485600 +0200
@@ -4,8 +4,12 @@ struct S {
 }
 control c(out bool z);
 package top(c _c);
+struct tuple_0 {
+    bit<32> field;
+    bit<32> field_0;
+}
 control test(out bool zout) {
-    tuple<bit<32>, bit<32>> p;
+    tuple_0 p;
     S q;
     apply {
         p = { 32w4, 32w5 };
