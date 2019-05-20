--- dumps/p4_16_samples/issue1006.p4/pruned/issue1006-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 17:30:28.574379300 +0200
+++ dumps/p4_16_samples/issue1006.p4/pruned/issue1006-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 17:30:28.576823600 +0200
@@ -6,8 +6,11 @@ struct foo {
 }
 control c();
 package top(c _c);
+struct tuple_0 {
+    bit<8> field;
+}
 control c1() {
-    @name("c1.reg0") R<tuple<bit<8>>>({ 8w1 }) reg0;
+    @name("c1.reg0") R<tuple_0>({ 8w1 }) reg0;
     @name("c1.reg1") R<foo>({ 8w1 }) reg1;
     apply {
     }
