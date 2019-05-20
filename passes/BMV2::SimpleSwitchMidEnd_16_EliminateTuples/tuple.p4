--- dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:32:30.751251400 +0200
+++ dumps/p4_16_samples/tuple.p4/pruned/tuple-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:32:30.756985300 +0200
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
