--- before_pass
+++ after_pass
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
-    tuple<bit<32>, bool> x_0;
+    tuple_0 x_0;
     apply {
         x_0 = { 32w10, false };
         f(x_0);
