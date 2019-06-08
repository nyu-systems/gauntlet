--- before_pass
+++ after_pass
@@ -15,15 +15,23 @@ control d(out bool b) {
     H tmp_0;
     apply {
         h_1.setValid();
-        h_1 = { 32w0 };
+        {
+            h_1.x = 32w0;
+        }
         s.h.setValid();
         s1.h.setValid();
-        s1.h = { 32w0 };
+        {
+            s1.h.x = 32w0;
+        }
         h3[0].setValid();
         h3[1].setValid();
-        h3[1] = { 32w1 };
+        {
+            h3[1].x = 32w1;
+        }
         tmp_0.setValid();
-        tmp_0 = { 32w0 };
+        {
+            tmp_0.x = 32w0;
+        }
         eout = tmp_0.isValid();
         b = h_1.isValid() && eout && h3[1].isValid() && s1.h.isValid();
     }
