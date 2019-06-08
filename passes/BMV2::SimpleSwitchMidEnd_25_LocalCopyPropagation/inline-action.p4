--- before_pass
+++ after_pass
@@ -1,16 +1,10 @@
 control p(inout bit<1> bt) {
-    bit<1> y0_0;
-    bit<1> y0_2;
     @name("p.b") action b_0() {
         {
-            y0_0 = bt;
-            y0_0 = y0_0 | 1w1;
-            bt = y0_0;
+            bt = bt | 1w1;
         }
         {
-            y0_2 = bt;
-            y0_2 = y0_2 | 1w1;
-            bt = y0_2;
+            bt = bt | 1w1;
         }
     }
     @name("p.t") table t {
