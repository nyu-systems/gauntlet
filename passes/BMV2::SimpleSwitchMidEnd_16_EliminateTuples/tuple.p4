--- before_pass
+++ after_pass
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
