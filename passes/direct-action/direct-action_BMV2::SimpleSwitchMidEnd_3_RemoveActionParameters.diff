--- before_pass
+++ after_pass
@@ -1,11 +1,13 @@
 control c(inout bit<16> y) {
     bit<32> x_0;
-    @name("c.a") action a(in bit<32> arg) {
+    bit<32> arg;
+    @name("c.a") action a() {
+        arg = x_0;
         y = (bit<16>)arg;
     }
     apply {
         x_0 = 32w2;
-        a(x_0);
+        a();
     }
 }
 control proto(inout bit<16> y);
