--- before_pass
+++ after_pass
@@ -1,7 +1,7 @@
 #include <core.p4>
 parser par(out bool b) {
     state start {
-        b = 32w6 == 32w0;
+        b = false;
         transition accept;
     }
 }
@@ -9,10 +9,10 @@ control c(out bool b) {
     bit<16> xv_0;
     bool b_1;
     @name("c.a") action a() {
-        xv_0 = -16w3;
+        xv_0 = 16w65533;
     }
     @name("c.a") action a_2() {
-        xv_0 = -16w0;
+        xv_0 = 16w0;
     }
     apply {
         a();
@@ -22,9 +22,9 @@ control c(out bool b) {
         b = b_1;
         xv_0 = 16w1;
         xv_0 = 16w1;
-        b = 16w1 == 16w0;
-        b_1 = 16w1 == 16w1;
-        b = 16w1 == 16w1;
+        b = false;
+        b_1 = true;
+        b = true;
         xv_0 = 16w1;
     }
 }
