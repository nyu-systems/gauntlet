--- before_pass
+++ after_pass
@@ -12,7 +12,7 @@ parser p_0(out bit<1> z) {
     }
     state start_0 {
         z = z1;
-        z = z & 1w0 & 1w1;
+        z = 1w0;
         transition accept;
     }
 }
