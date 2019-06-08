--- before_pass
+++ after_pass
@@ -4,13 +4,7 @@ package m(simple n);
 parser p_0(out bit<1> z) {
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
         z = 1w0;
         transition accept;
