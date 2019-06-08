--- before_pass
+++ after_pass
@@ -1,12 +1,12 @@
 control c(inout bit<32> x) {
     apply {
         x = 32w10;
-        if (x == 32w10) {
-            x = x + 32w2;
-            x = x + 32w4294967290;
+        if (32w10 == 32w10) {
+            x = 32w10 + 32w2;
+            x = 32w10 + 32w2 + 32w4294967290;
         }
         else 
-            x = x << 2;
+            x = 32w10 << 2;
     }
 }
 control n(inout bit<32> x);
