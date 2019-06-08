--- before_pass
+++ after_pass
@@ -1,10 +1,12 @@
 control c() {
     bit<32> x;
-    @name("c.b") action b_0(out bit<32> arg) {
+    bit<32> arg;
+    @name("c.b") action b_0() {
         arg = 32w2;
+        x = arg;
     }
     apply {
-        b_0(x);
+        b_0();
     }
 }
 control proto();
