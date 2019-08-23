--- before_pass
+++ after_pass
@@ -9,8 +9,8 @@ package top(c _c);
 control d(out bool b) {
     H h_0;
     H[2] h3_0;
-    S s_0;
-    S s1_0;
+    H s_0_h;
+    H s1_0_h;
     bool eout_0;
     H tmp;
     apply {
@@ -18,10 +18,10 @@ control d(out bool b) {
         {
             h_0.x = 32w0;
         }
-        s_0.h.setValid();
-        s1_0.h.setValid();
+        s_0_h.setValid();
+        s1_0_h.setValid();
         {
-            s1_0.h.x = 32w0;
+            s1_0_h.x = 32w0;
         }
         h3_0[0].setValid();
         h3_0[1].setValid();
@@ -33,7 +33,7 @@ control d(out bool b) {
             tmp.x = 32w0;
         }
         eout_0 = tmp.isValid();
-        b = h_0.isValid() && eout_0 && h3_0[1].isValid() && s1_0.h.isValid();
+        b = h_0.isValid() && eout_0 && h3_0[1].isValid() && s1_0_h.isValid();
     }
 }
 top(d()) main;
