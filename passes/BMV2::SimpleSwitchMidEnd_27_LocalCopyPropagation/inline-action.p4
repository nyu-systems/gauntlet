--- before_pass
+++ after_pass
@@ -1,16 +1,10 @@
 control p(inout bit<1> bt) {
-    bit<1> y0;
-    bit<1> y0_1;
     @name("p.b") action b() {
         {
-            y0 = bt;
-            y0 = y0 | 1w1;
-            bt = y0;
+            bt = bt | 1w1;
         }
         {
-            y0_1 = bt;
-            y0_1 = y0_1 | 1w1;
-            bt = y0_1;
+            bt = bt | 1w1;
         }
     }
     @name("p.t") table t_0 {
