--- before_pass
+++ after_pass
@@ -1,10 +1,12 @@
 control c() {
     bit<32> x_0;
-    @name("c.b") action b(out bit<32> arg) {
+    bit<32> arg;
+    @name("c.b") action b() {
         arg = 32w2;
+        x_0 = arg;
     }
     apply {
-        b(x_0);
+        b();
     }
 }
 control proto();
