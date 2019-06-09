--- before_pass
+++ after_pass
@@ -19,15 +19,23 @@ control c(out bool b) {
     bool b_0;
     bit<16> x_2;
     bool b_1;
-    @name("c.a") action a(in bit<16> bi, out bit<16> mb) {
+    bit<16> bi;
+    bit<16> mb;
+    @name("c.a") action a() {
+        bi = 16w3;
         mb = -bi;
+        xv_0 = mb;
     }
-    @name("c.a") action a_2(in bit<16> bi_1, out bit<16> mb_1) {
+    bit<16> bi_1;
+    bit<16> mb_1;
+    @name("c.a") action a_2() {
+        bi_1 = 16w0;
         mb_1 = -bi_1;
+        xv_0 = mb_1;
     }
     apply {
-        a(bi = 16w3, mb = xv_0);
-        a_2(mb = xv_0, bi = 16w0);
+        a();
+        a_2();
         x_1 = xv_0;
         b_0 = x_1 == 16w0;
         b = b_0;
