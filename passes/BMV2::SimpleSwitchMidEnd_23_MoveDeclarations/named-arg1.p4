--- before_pass
+++ after_pass
@@ -19,13 +19,13 @@ control c(out bool b) {
     bool b_3;
     bit<16> bi;
     bit<16> mb;
+    bit<16> bi_1;
+    bit<16> mb_1;
     @name("c.a") action a_0() {
         bi = 16w3;
         mb = -bi;
         xv = mb;
     }
-    bit<16> bi_1;
-    bit<16> mb_1;
     @name("c.a") action a_2() {
         bi_1 = 16w0;
         mb_1 = -bi_1;
