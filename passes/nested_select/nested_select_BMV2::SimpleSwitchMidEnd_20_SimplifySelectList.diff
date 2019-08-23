--- before_pass
+++ after_pass
@@ -3,9 +3,9 @@ parser p() {
     bit<8> x_0;
     state start {
         x_0 = 8w5;
-        transition select(x_0, x_0, { x_0, x_0 }, x_0) {
-            (8w0, 8w0, { 8w0, 8w0 }, 8w0): accept;
-            (8w1, 8w1, default, 8w1): accept;
+        transition select(x_0, x_0, x_0, x_0, x_0) {
+            (8w0, 8w0, 8w0, 8w0, 8w0): accept;
+            (8w1, 8w1, default, default, 8w1): accept;
             default: reject;
         }
     }
