--- before_pass
+++ after_pass
@@ -1,9 +1,7 @@
 #include <core.p4>
 parser p() {
-    bit<8> x_0;
     state start {
-        x_0 = 8w5;
-        transition select(x_0, x_0, x_0, x_0, x_0) {
+        transition select(8w5, 8w5, 8w5, 8w5, 8w5) {
             (8w0, 8w0, 8w0, 8w0, 8w0): accept;
             (8w1, 8w1, default, default, 8w1): accept;
             default: reject;
