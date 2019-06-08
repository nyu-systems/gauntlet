--- before_pass
+++ after_pass
@@ -1,19 +1,15 @@
 extern bit<32> f(in bit<32> x);
 control c(inout bit<32> r) {
     bit<32> tmp_4;
-    bool tmp_5;
     bool tmp_6;
     bit<32> tmp_7;
-    bool tmp_8;
     apply {
         tmp_4 = f(32w2);
-        tmp_5 = tmp_4 > 32w0;
-        if (!tmp_5) 
+        if (!(tmp_4 > 32w0)) 
             tmp_6 = false;
         else {
             tmp_7 = f(32w3);
-            tmp_8 = tmp_7 < 32w0;
-            tmp_6 = tmp_8;
+            tmp_6 = tmp_7 < 32w0;
         }
         if (tmp_6) 
             r = 32w1;
