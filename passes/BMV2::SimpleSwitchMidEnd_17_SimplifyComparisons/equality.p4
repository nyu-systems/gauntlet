--- before_pass
+++ after_pass
@@ -19,13 +19,13 @@ control c(out bit<1> x) {
         if (a_0 == b_0) 
             x = 1w1;
         else 
-            if (h1_0 == h2_0) 
+            if (!h1_0.isValid() && !h2_0.isValid() || h1_0.isValid() && h2_0.isValid() && h1_0.a == h2_0.a && h1_0.b == h2_0.b) 
                 x = 1w1;
             else 
-                if (s1_0 == s2_0) 
+                if (true && s1_0.a == s2_0.a && (!s1_0.h.isValid() && !s2_0.h.isValid() || s1_0.h.isValid() && s2_0.h.isValid() && s1_0.h.a == s2_0.h.a && s1_0.h.b == s2_0.h.b)) 
                     x = 1w1;
                 else 
-                    if (a1_0 == a2_0) 
+                    if (true && (!a1_0[0].isValid() && !a2_0[0].isValid() || a1_0[0].isValid() && a2_0[0].isValid() && a1_0[0].a == a2_0[0].a && a1_0[0].b == a2_0[0].b) && (!a1_0[1].isValid() && !a2_0[1].isValid() || a1_0[1].isValid() && a2_0[1].isValid() && a1_0[1].a == a2_0[1].a && a1_0[1].b == a2_0[1].b)) 
                         x = 1w1;
                     else 
                         x = 1w0;
