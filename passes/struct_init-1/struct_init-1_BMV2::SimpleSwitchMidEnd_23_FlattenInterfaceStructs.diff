--- before_pass
+++ after_pass
@@ -5,14 +5,14 @@ header H {
     bit<32> b;
 }
 struct metadata_t {
-    PortId_t foo;
+    bit<9> _foo__v0;
 }
 control I(inout metadata_t meta) {
     H h_0;
     apply {
         h_0.setValid();
-        if (true && meta.foo._v == 9w192) {
-            meta.foo._v = meta.foo._v + 9w1;
+        if (true && meta._foo__v0 == 9w192) {
+            meta._foo__v0 = meta._foo__v0 + 9w1;
             h_0.setValid();
             {
                 h_0.b = 32w2;
