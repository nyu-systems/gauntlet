--- before_pass
+++ after_pass
@@ -2,13 +2,7 @@
 parser par(out bool b) {
     bit<32> x_0;
     state start {
-        transition adder_0_start;
-    }
-    state adder_0_start {
         x_0 = 32w6;
-        transition start_0;
-    }
-    state start_0 {
         b = x_0 == 32w0;
         transition accept;
     }
