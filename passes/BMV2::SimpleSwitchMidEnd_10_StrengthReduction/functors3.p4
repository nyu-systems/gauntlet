--- before_pass
+++ after_pass
@@ -10,7 +10,7 @@ parser p_0(out bit<1> z) {
         transition start_0;
     }
     state start_0 {
-        z = z & 1w0 & 1w1;
+        z = 1w0;
         transition accept;
     }
 }
