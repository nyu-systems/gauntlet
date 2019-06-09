--- before_pass
+++ after_pass
@@ -5,34 +5,18 @@ extern bit<1> f(inout bit<1> x, in bit<1
 control c(out H[2] h);
 package top(c _c);
 control my(out H[2] s) {
-    bit<32> a_0;
-    bit<32> tmp;
-    bit<32> tmp_0;
-    bit<32> tmp_1;
-    bit<32> tmp_2;
     bit<1> tmp_3;
-    bit<1> tmp_4;
-    bit<32> tmp_5;
     bit<1> tmp_6;
     bit<1> tmp_8;
-    bit<1> tmp_9;
     @name("my.act") action act() {
-        a_0 = 32w0;
-        tmp = a_0;
-        s[tmp].z = 1w1;
-        tmp_0 = a_0 + 32w1;
-        tmp_1 = tmp_0;
-        s[tmp_1].z = 1w0;
-        tmp_2 = a_0;
-        tmp_3 = s[tmp_2].z;
+        s[32w0].z = 1w1;
+        s[32w0 + 32w1].z = 1w0;
+        tmp_3 = s[32w0].z;
         tmp_8 = f(tmp_3, 1w0);
-        tmp_4 = tmp_8;
-        s[tmp_2].z = tmp_3;
-        a_0 = (bit<32>)tmp_4;
-        tmp_5 = a_0;
-        tmp_6 = s[tmp_5].z;
-        tmp_9 = f(tmp_6, 1w1);
-        s[tmp_5].z = tmp_6;
+        s[32w0].z = tmp_3;
+        tmp_6 = s[(bit<32>)tmp_8].z;
+        f(tmp_6, 1w1);
+        s[(bit<32>)tmp_8].z = tmp_6;
     }
     @name("my.tbl_act") table tbl_act_0 {
         actions = {
