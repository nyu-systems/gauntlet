--- before_pass
+++ after_pass
@@ -9,8 +9,8 @@ package top(c _c);
 control d(out bool b) {
     H h_1;
     H[2] h3;
-    S s;
-    S s1;
+    H s_h;
+    H s1_h;
     bool eout;
     H tmp_0;
     apply {
@@ -18,10 +18,10 @@ control d(out bool b) {
         {
             h_1.x = 32w0;
         }
-        s.h.setValid();
-        s1.h.setValid();
+        s_h.setValid();
+        s1_h.setValid();
         {
-            s1.h.x = 32w0;
+            s1_h.x = 32w0;
         }
         h3[0].setValid();
         h3[1].setValid();
@@ -33,7 +33,7 @@ control d(out bool b) {
             tmp_0.x = 32w0;
         }
         eout = tmp_0.isValid();
-        b = h_1.isValid() && eout && h3[1].isValid() && s1.h.isValid();
+        b = h_1.isValid() && eout && h3[1].isValid() && s1_h.isValid();
     }
 }
 top(d()) main;
