--- before_pass
+++ after_pass
@@ -2,23 +2,17 @@ control c(inout bit<32> x) {
     bit<32> tmp_6;
     bit<32> tmp_10;
     apply {
-        {
-            if (x > x + 32w1) 
-                tmp_10 = x + 32w1;
-            else 
-                tmp_10 = x;
-        }
+        if (x > x + 32w1) 
+            tmp_10 = x + 32w1;
+        else 
+            tmp_10 = x;
         tmp_6 = tmp_10;
-        {
-            if (x > x + 32w4294967295) 
-                tmp_10 = x + 32w4294967295;
-            else 
-                tmp_10 = x;
-        }
-        {
-            if (!(tmp_6 > tmp_10)) 
-                tmp_10 = tmp_6;
-        }
+        if (x > x + 32w4294967295) 
+            tmp_10 = x + 32w4294967295;
+        else 
+            tmp_10 = x;
+        if (!(tmp_6 > tmp_10)) 
+            tmp_10 = tmp_6;
         x = tmp_10;
     }
 }
