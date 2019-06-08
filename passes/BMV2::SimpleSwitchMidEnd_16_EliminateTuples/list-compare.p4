--- dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:34:07.902378400 +0200
+++ dumps/pruned/list-compare-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:34:07.904435900 +0200
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
