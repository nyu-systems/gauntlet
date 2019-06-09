--- before_pass
+++ after_pass
@@ -8,7 +8,7 @@ control my(out H[2] s) {
     bit<32> tmp;
     apply {
         s[32w0].z = 1w1;
-        s[32w0 + 32w1].z = 1w0;
+        s[32w1].z = 1w0;
         tmp = f(s[32w0].z, 1w0);
         f(s[tmp].z, 1w1);
     }
