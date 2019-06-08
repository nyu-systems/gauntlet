--- before_pass
+++ after_pass
@@ -2,13 +2,7 @@
 parser p(out bit<1> z) {
     bit<1> z1;
     state start {
-        transition p1_0_start;
-    }
-    state p1_0_start {
         z1 = 1w0;
-        transition start_0;
-    }
-    state start_0 {
         z = z1;
         transition accept;
     }
