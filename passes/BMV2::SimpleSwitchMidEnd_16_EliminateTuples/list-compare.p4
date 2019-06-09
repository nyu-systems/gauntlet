--- before_pass
+++ after_pass
@@ -4,8 +4,12 @@ struct S {
 }
 control c(out bool z);
 package top(c _c);
+struct tuple_0 {
+    bit<32> field;
+    bit<32> field_0;
+}
 control test(out bool zout) {
-    tuple<bit<32>, bit<32>> p_0;
+    tuple_0 p_0;
     S q_0;
     apply {
         p_0 = { 32w4, 32w5 };
