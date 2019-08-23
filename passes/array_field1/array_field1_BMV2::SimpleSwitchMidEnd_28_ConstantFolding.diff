--- before_pass
+++ after_pass
@@ -10,7 +10,7 @@ control my(out H[2] s) {
     bit<1> tmp_8;
     @name("my.act") action act() {
         s[32w0].z = 1w1;
-        s[32w0 + 32w1].z = 1w0;
+        s[32w1].z = 1w0;
         tmp_3 = s[32w0].z;
         tmp_8 = f(tmp_3, 1w0);
         s[32w0].z = tmp_3;
