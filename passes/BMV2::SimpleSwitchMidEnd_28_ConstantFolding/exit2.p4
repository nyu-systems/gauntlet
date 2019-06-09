--- before_pass
+++ after_pass
@@ -7,10 +7,7 @@ control ctrl(out bit<32> c) {
     }
     apply {
         c = 32w2;
-        if (32w0 == 32w0) 
-            e();
-        else 
-            e_2();
+        e();
         c = 32w5;
     }
 }
