--- before_pass
+++ after_pass
@@ -1,10 +1,8 @@
 control c(inout bit<32> x) {
     apply {
         x = 32w10;
-        {
-            x = 32w12;
-            x = 32w6;
-        }
+        x = 32w12;
+        x = 32w6;
     }
 }
 control n(inout bit<32> x);
