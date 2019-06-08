--- before_pass
+++ after_pass
@@ -1,8 +1,6 @@
 control c(inout bit<32> x) {
-    bit<32> arg_1;
     @name("c.a") action a_0() {
-        arg_1 = 32w10;
-        x = arg_1;
+        x = 32w10;
     }
     @name("c.t") table t {
         actions = {
