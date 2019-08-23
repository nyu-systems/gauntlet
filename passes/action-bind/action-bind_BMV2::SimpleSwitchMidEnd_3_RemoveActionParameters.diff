--- before_pass
+++ after_pass
@@ -1,12 +1,15 @@
 control c(inout bit<32> x) {
-    @name("c.a") action a(inout bit<32> b, bit<32> d) {
+    bit<32> b;
+    @name("c.a") action a(bit<32> d) {
+        b = x;
         b = d;
+        x = b;
     }
     @name("c.t") table t_0 {
         actions = {
-            a(x);
+            a();
         }
-        default_action = a(x, 32w0);
+        default_action = a(32w0);
     }
     apply {
         t_0.apply();
