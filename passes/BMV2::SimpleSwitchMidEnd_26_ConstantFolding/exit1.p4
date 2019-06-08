--- before_pass
+++ after_pass
@@ -1,9 +1,6 @@
 control ctrl() {
     apply {
-        if (32w0 == 32w0) 
-            exit;
-        else 
-            exit;
+        exit;
     }
 }
 control noop();
