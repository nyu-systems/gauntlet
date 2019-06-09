--- before_pass
+++ after_pass
@@ -15,13 +15,13 @@ control c(out bool b) {
     bool b_1;
     bit<16> bi;
     bit<16> mb;
+    bit<16> bi_1;
+    bit<16> mb_1;
     @name("c.a") action a() {
         bi = 16w3;
         mb = -bi;
         xv_0 = mb;
     }
-    bit<16> bi_1;
-    bit<16> mb_1;
     @name("c.a") action a_2() {
         bi_1 = 16w0;
         mb_1 = -bi_1;
