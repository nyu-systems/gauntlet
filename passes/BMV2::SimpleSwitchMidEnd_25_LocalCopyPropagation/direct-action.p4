--- before_pass
+++ after_pass
@@ -1,9 +1,7 @@
 control c(inout bit<16> y) {
     bit<32> x;
-    bit<32> arg;
     @name("c.a") action a_0() {
-        arg = x;
-        y = (bit<16>)arg;
+        y = (bit<16>)x;
     }
     apply {
         x = 32w2;
