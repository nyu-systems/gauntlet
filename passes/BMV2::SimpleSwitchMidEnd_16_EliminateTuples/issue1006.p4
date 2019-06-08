--- dumps/pruned/issue1006-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-06-08 18:32:11.925664300 +0200
+++ dumps/pruned/issue1006-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-06-08 18:32:11.930094800 +0200
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
