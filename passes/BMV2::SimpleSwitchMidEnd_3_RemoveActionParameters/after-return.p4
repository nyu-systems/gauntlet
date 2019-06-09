--- before_pass
+++ after_pass
@@ -1,7 +1,8 @@
 control ctrl() {
     bit<32> a_0;
+    bool hasReturned;
     apply {
-        bool hasReturned = false;
+        hasReturned = false;
         a_0 = 32w0;
         if (a_0 == 32w0) 
             hasReturned = true;
