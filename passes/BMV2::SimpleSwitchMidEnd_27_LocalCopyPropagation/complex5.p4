--- before_pass
+++ after_pass
@@ -1,11 +1,9 @@
 extern bit<32> f(in bit<32> x);
 control c(inout bit<32> r) {
     bit<32> tmp;
-    bool tmp_0;
     apply {
         tmp = f(32w2);
-        tmp_0 = tmp > 32w0;
-        if (tmp_0) 
+        if (tmp > 32w0) 
             r = 32w1;
         else 
             r = 32w2;
