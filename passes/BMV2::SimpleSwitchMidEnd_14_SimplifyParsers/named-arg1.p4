--- before_pass
+++ after_pass
@@ -5,13 +5,7 @@ parser par(out bool b) {
     bit<32> x_4;
     state start {
         y = 32w0;
-        transition adder_0_start;
-    }
-    state adder_0_start {
         x_4 = y + 32w6;
-        transition start_0;
-    }
-    state start_0 {
         x = x_4;
         b = x == 32w0;
         transition accept;
