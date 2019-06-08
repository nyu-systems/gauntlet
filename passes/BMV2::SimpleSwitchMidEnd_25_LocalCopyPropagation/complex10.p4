--- before_pass
+++ after_pass
@@ -1,29 +1,23 @@
 extern bit<32> f(in bit<32> x);
 control c(inout bit<32> r) {
     bit<32> tmp_7;
-    bool tmp_8;
     bool tmp_9;
     bit<32> tmp_10;
-    bool tmp_11;
     bool tmp_12;
     bit<32> tmp_13;
-    bool tmp_14;
     apply {
         tmp_7 = f(32w2);
-        tmp_8 = tmp_7 > 32w0;
-        if (!tmp_8) 
+        if (!(tmp_7 > 32w0)) 
             tmp_9 = false;
         else {
             tmp_10 = f(32w3);
-            tmp_11 = tmp_10 < 32w0;
-            tmp_9 = tmp_11;
+            tmp_9 = tmp_10 < 32w0;
         }
         if (tmp_9) 
             tmp_12 = true;
         else {
             tmp_13 = f(32w5);
-            tmp_14 = tmp_13 == 32w2;
-            tmp_12 = tmp_14;
+            tmp_12 = tmp_13 == 32w2;
         }
         if (tmp_12) 
             r = 32w1;
