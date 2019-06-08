--- before_pass
+++ after_pass
@@ -3,9 +3,9 @@ parser p() {
     bit<8> x;
     state start {
         x = 8w5;
-        transition select(x, x, { x, x }, x) {
-            (8w0, 8w0, { 8w0, 8w0 }, 8w0): accept;
-            (8w1, 8w1, default, 8w1): accept;
+        transition select(x, x, x, x, x) {
+            (8w0, 8w0, 8w0, 8w0, 8w0): accept;
+            (8w1, 8w1, default, default, 8w1): accept;
             default: reject;
         }
     }
