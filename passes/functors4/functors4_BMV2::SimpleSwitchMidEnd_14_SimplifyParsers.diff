--- before_pass
+++ after_pass
@@ -1,13 +1,7 @@
 #include <core.p4>
 parser p(out bit<1> z) {
     state start {
-        transition p1_0_start;
-    }
-    state p1_0_start {
         z = 1w0;
-        transition start_0;
-    }
-    state start_0 {
         transition accept;
     }
 }
