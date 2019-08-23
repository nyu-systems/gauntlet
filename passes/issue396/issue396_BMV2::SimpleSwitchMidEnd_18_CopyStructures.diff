--- before_pass
+++ after_pass
@@ -15,15 +15,23 @@ control d(out bool b) {
     H tmp;
     apply {
         h_0.setValid();
-        h_0 = H {x = 32w0};
+        {
+            h_0.x = 32w0;
+        }
         s_0.h.setValid();
         s1_0.h.setValid();
-        s1_0.h = H {x = 32w0};
+        {
+            s1_0.h.x = 32w0;
+        }
         h3_0[0].setValid();
         h3_0[1].setValid();
-        h3_0[1] = H {x = 32w1};
+        {
+            h3_0[1].x = 32w1;
+        }
         tmp.setValid();
-        tmp = H {x = 32w0};
+        {
+            tmp.x = 32w0;
+        }
         eout_0 = tmp.isValid();
         b = h_0.isValid() && eout_0 && h3_0[1].isValid() && s1_0.h.isValid();
     }
