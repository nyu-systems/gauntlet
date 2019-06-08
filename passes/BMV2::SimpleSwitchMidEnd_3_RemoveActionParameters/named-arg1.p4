--- before_pass
+++ after_pass
@@ -23,15 +23,23 @@ control c(out bool b) {
     bool b_2;
     bit<16> x_6;
     bool b_3;
-    @name("c.a") action a_0(in bit<16> bi, out bit<16> mb) {
+    bit<16> bi;
+    bit<16> mb;
+    @name("c.a") action a_0() {
+        bi = 16w3;
         mb = -bi;
+        xv = mb;
     }
-    @name("c.a") action a_2(in bit<16> bi_1, out bit<16> mb_1) {
+    bit<16> bi_1;
+    bit<16> mb_1;
+    @name("c.a") action a_2() {
+        bi_1 = 16w0;
         mb_1 = -bi_1;
+        xv = mb_1;
     }
     apply {
-        a_0(bi = 16w3, mb = xv);
-        a_2(mb = xv, bi = 16w0);
+        a_0();
+        a_2();
         x_5 = xv;
         b_2 = x_5 == 16w0;
         b = b_2;
