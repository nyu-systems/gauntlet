--- before_pass
+++ after_pass
@@ -1,11 +1,15 @@
 extern void f<T>(in T data);
 control proto();
 package top(proto _p);
+struct tuple_0 {
+    bit<32> field;
+    bool    field_0;
+}
 control c() {
-    tuple<bit<32>, bool> x_0;
+    tuple_0 x_0;
     apply {
         x_0 = { 32w10, false };
-        f<tuple<bit<32>, bool>>(x_0);
+        f<tuple_0>(x_0);
     }
 }
 top(c()) main;
