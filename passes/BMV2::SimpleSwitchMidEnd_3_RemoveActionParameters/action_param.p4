--- before_pass
+++ after_pass
@@ -1,12 +1,14 @@
 control c(inout bit<32> x) {
-    @name("c.a") action a_0(in bit<32> arg_1) {
+    bit<32> arg_1;
+    @name("c.a") action a_0() {
+        arg_1 = 32w10;
         x = arg_1;
     }
     @name("c.t") table t {
         actions = {
-            a_0(32w10);
+            a_0();
         }
-        default_action = a_0(32w10);
+        default_action = a_0();
     }
     apply {
         t.apply();
