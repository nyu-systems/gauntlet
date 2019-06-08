--- before_pass
+++ after_pass
@@ -1,7 +1,8 @@
 control ctrl() {
     bit<32> a;
+    bool hasReturned_0;
     apply {
-        bool hasReturned_0 = false;
+        hasReturned_0 = false;
         a = 32w0;
         if (a == 32w0) 
             hasReturned_0 = true;
