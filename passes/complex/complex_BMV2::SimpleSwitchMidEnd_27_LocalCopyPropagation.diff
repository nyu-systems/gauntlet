--- before_pass
+++ after_pass
@@ -1,12 +1,10 @@
 extern bit<32> f(in bit<32> x);
 control c(inout bit<32> r) {
     bit<32> tmp;
-    bit<32> tmp_0;
     bit<32> tmp_1;
     apply {
         tmp = f(32w5);
-        tmp_0 = tmp;
-        tmp_1 = f(tmp_0);
+        tmp_1 = f(tmp);
         r = tmp_1;
     }
 }
