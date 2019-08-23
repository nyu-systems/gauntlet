--- before_pass
+++ after_pass
@@ -1,9 +1,7 @@
 control c(inout bit<16> y) {
     bit<32> x_0;
-    bit<32> arg;
     @name("c.a") action a() {
-        arg = x_0;
-        y = (bit<16>)arg;
+        y = (bit<16>)x_0;
     }
     apply {
         x_0 = 32w10;
