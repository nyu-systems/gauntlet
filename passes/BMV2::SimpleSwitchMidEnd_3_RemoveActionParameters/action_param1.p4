--- before_pass
+++ after_pass
@@ -1,9 +1,11 @@
 control c(inout bit<32> x) {
-    @name("c.a") action a(in bit<32> arg_1) {
+    bit<32> arg_1;
+    @name("c.a") action a() {
+        arg_1 = 32w15;
         x = arg_1;
     }
     apply {
-        a(32w15);
+        a();
     }
 }
 control proto(inout bit<32> arg);
