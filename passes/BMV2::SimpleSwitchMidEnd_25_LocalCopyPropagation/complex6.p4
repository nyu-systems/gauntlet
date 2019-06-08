--- before_pass
+++ after_pass
@@ -1,16 +1,12 @@
 extern bit<32> f(in bit<32> x);
 control c(inout bit<32> r) {
     bit<32> tmp_3;
-    bool tmp_4;
     bit<32> tmp_5;
-    bool tmp_6;
     apply {
         tmp_5 = f(32w2);
-        tmp_6 = tmp_5 > 32w0;
-        if (tmp_6) {
+        if (tmp_5 > 32w0) {
             tmp_3 = f(32w2);
-            tmp_4 = tmp_3 < 32w2;
-            if (tmp_4) 
+            if (tmp_3 < 32w2) 
                 r = 32w1;
             else 
                 r = 32w3;
