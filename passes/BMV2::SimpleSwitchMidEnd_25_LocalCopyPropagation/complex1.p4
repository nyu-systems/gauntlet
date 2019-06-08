--- before_pass
+++ after_pass
@@ -1,20 +1,14 @@
 extern bit<32> f(in bit<32> x, in bit<32> y);
 control c(inout bit<32> r) {
     bit<32> tmp_6;
-    bit<32> tmp_7;
     bit<32> tmp_8;
-    bit<32> tmp_9;
     bit<32> tmp_10;
-    bit<32> tmp_11;
     bit<32> tmp_12;
     apply {
         tmp_6 = f(32w5, 32w2);
-        tmp_7 = tmp_6;
         tmp_8 = f(32w2, 32w3);
-        tmp_9 = tmp_8;
-        tmp_10 = f(32w6, tmp_9);
-        tmp_11 = tmp_10;
-        tmp_12 = f(tmp_7, tmp_11);
+        tmp_10 = f(32w6, tmp_8);
+        tmp_12 = f(tmp_6, tmp_10);
         r = tmp_12;
     }
 }
