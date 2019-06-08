--- before_pass
+++ after_pass
@@ -1,9 +1,11 @@
 control c(inout bit<32> x) {
-    @name("c.a") action a_0(in bit<32> arg_1) {
+    bit<32> arg_1;
+    @name("c.a") action a_0() {
+        arg_1 = 32w15;
         x = arg_1;
     }
     apply {
-        a_0(32w15);
+        a_0();
     }
 }
 control proto(inout bit<32> arg);
