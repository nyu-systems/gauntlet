--- before_pass
+++ after_pass
@@ -1,12 +1,14 @@
 control c(inout bit<32> x) {
-    @name("c.a") action a(in bit<32> arg_1) {
+    bit<32> arg_1;
+    @name("c.a") action a() {
+        arg_1 = 32w10;
         x = arg_1;
     }
     @name("c.t") table t_0 {
         actions = {
-            a(32w10);
+            a();
         }
-        default_action = a(32w10);
+        default_action = a();
     }
     apply {
         t_0.apply();
