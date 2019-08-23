--- before_pass
+++ after_pass
@@ -1,11 +1,7 @@
 #include <core.p4>
 parser p() {
     state start {
-        transition select(8w5, 8w5, 8w5, 8w5, 8w5) {
-            (8w0, 8w0, 8w0, 8w0, 8w0): accept;
-            (8w1, 8w1, default, default, 8w1): accept;
-            default: reject;
-        }
+        transition reject;
     }
 }
 parser s();
