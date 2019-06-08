--- dumps/pruned/inline-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:31:51.333091000 +0200
+++ dumps/pruned/inline-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:31:51.382237600 +0200
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
