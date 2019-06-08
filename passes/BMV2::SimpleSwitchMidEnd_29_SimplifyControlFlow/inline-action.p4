--- before_pass
+++ after_pass
@@ -1,11 +1,7 @@
 control p(inout bit<1> bt) {
     @name("p.b") action b_0() {
-        {
-            bt = bt | 1w1;
-        }
-        {
-            bt = bt | 1w1;
-        }
+        bt = bt | 1w1;
+        bt = bt | 1w1;
     }
     @name("p.t") table t {
         actions = {
