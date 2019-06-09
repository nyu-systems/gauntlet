--- before_pass
+++ after_pass
@@ -5,16 +5,12 @@ extern bit<32> f(inout bit<1> x, in bit<
 control c(out H[2] h);
 package top(c _c);
 control my(out H[2] s) {
-    bit<32> a_0;
     bit<32> tmp;
-    bit<32> tmp_0;
     apply {
-        a_0 = 32w0;
-        s[a_0].z = 1w1;
-        s[a_0 + 32w1].z = 1w0;
-        tmp = f(s[a_0].z, 1w0);
-        a_0 = tmp;
-        tmp_0 = f(s[a_0].z, 1w1);
+        s[32w0].z = 1w1;
+        s[32w0 + 32w1].z = 1w0;
+        tmp = f(s[32w0].z, 1w0);
+        f(s[tmp].z, 1w1);
     }
 }
 top(my()) main;
