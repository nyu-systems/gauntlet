--- before_pass
+++ after_pass
@@ -33,7 +33,7 @@ control my() {
         tmp_22 = g(a);
         a = tmp_22;
         tmp_23 = g(a[0:0]);
-        a[0:0] = tmp_23;
+        a = a & ~1w0x1 | (bit<1>)tmp_23 << 0 & 1w0x1;
         g(a);
     }
 }
