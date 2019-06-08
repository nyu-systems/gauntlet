--- before_pass
+++ after_pass
@@ -15,10 +15,10 @@ control c(out bool b) {
     bit<16> xv;
     bool b_3;
     @name("c.a") action a_0() {
-        xv = -16w3;
+        xv = 16w65533;
     }
     @name("c.a") action a_2() {
-        xv = -16w0;
+        xv = 16w0;
     }
     apply {
         a_0();
@@ -28,9 +28,9 @@ control c(out bool b) {
         b = b_3;
         xv = 16w1;
         xv = 16w1;
-        b = 16w1 == 16w0;
-        b_3 = 16w1 == 16w1;
-        b = 16w1 == 16w1;
+        b = false;
+        b_3 = true;
+        b = true;
         xv = 16w1;
     }
 }
