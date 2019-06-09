--- before_pass
+++ after_pass
@@ -1,9 +1,6 @@
 control c(inout bit<32> x) {
-    bit<32> b;
     @name("c.a") action a(bit<32> d) {
-        b = x;
-        b = d;
-        x = b;
+        x = d;
     }
     @name("c.t") table t_0 {
         actions = {
