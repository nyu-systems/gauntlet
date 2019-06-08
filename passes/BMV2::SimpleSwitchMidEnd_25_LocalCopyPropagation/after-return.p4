--- before_pass
+++ after_pass
@@ -1,13 +1,5 @@
 control ctrl() {
-    bit<32> a;
-    bool hasReturned_0;
     apply {
-        hasReturned_0 = false;
-        a = 32w0;
-        if (a == 32w0) 
-            hasReturned_0 = true;
-        else 
-            hasReturned_0 = true;
     }
 }
 control noop();
