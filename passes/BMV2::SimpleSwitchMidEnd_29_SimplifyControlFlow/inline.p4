--- before_pass
+++ after_pass
@@ -1,10 +1,6 @@
 control p(out bit<1> y) {
     bit<1> x_3;
     @name("p.b") action b_0() {
-        {
-        }
-        {
-        }
         y = x_3 & x_3 & (x_3 & x_3) & (x_3 & x_3 & (x_3 & x_3));
     }
     apply {
