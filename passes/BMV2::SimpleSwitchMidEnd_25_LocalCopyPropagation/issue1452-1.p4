--- before_pass
+++ after_pass
@@ -1,9 +1,5 @@
 control c() {
-    bit<32> x;
-    bit<32> arg;
     @name("c.b") action b_0() {
-        arg = 32w2;
-        x = arg;
     }
     apply {
         b_0();
