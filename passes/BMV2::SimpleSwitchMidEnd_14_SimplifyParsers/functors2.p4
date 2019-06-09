--- before_pass
+++ after_pass
@@ -6,27 +6,9 @@ parser p2_0(out bit<2> z2) {
     bit<2> x2_0;
     bit<2> x3_0;
     state start {
-        transition p1_0_start;
-    }
-    state p1_0_start {
         x1_0 = 2w0;
-        transition start_0;
-    }
-    state start_0 {
-        transition p1_1_start;
-    }
-    state p1_1_start {
         x2_0 = 2w1;
-        transition start_1;
-    }
-    state start_1 {
-        transition p1_2_start;
-    }
-    state p1_2_start {
         x3_0 = 2w2;
-        transition start_2;
-    }
-    state start_2 {
         z2 = 2w3 | x1_0 | x2_0 | x3_0;
         transition accept;
     }
