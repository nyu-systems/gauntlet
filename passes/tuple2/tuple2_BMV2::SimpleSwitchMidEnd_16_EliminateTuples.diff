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
-    tuple<bit<32>, bool> x;
+    tuple_0 x;
     apply {
         x = { 32w10, false };
-        f<tuple<bit<32>, bool>>(x);
+        f<tuple_0>(x);
     }
 }
 top(c()) main;
