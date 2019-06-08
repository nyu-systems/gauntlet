--- before_pass
+++ after_pass
@@ -1,8 +1,6 @@
 control ctrl() {
-    bit<32> a;
     apply {
-        a = 32w0;
-        if (a == 32w0) 
+        if (32w0 == 32w0) 
             exit;
         else 
             exit;
