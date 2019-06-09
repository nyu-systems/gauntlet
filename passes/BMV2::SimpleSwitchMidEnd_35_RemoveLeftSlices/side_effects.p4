--- before_pass
+++ after_pass
@@ -33,7 +33,7 @@ control my() {
         tmp_9 = g(a_0);
         a_0 = tmp_9;
         tmp_10 = g(a_0[0:0]);
-        a_0[0:0] = tmp_10;
+        a_0 = a_0 & ~1w0x1 | (bit<1>)tmp_10 << 0 & 1w0x1;
         g(a_0);
     }
 }
