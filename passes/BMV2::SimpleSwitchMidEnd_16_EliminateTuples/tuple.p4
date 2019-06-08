--- dumps/pruned/tuple-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:34:17.493974800 +0200
+++ dumps/pruned/tuple-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:34:17.496074100 +0200
@@ -4,8 +4,12 @@ struct S {
 }
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
     }
