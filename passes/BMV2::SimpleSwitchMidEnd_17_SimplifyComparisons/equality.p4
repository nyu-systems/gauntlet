--- before_pass
+++ after_pass
@@ -19,13 +19,13 @@ control c(out bit<1> x) {
         if (a_1 == b_1) 
             x = 1w1;
         else 
-            if (h1 == h2) 
+            if (!h1.isValid() && !h2.isValid() || h1.isValid() && h2.isValid() && h1.a == h2.a && h1.b == h2.b) 
                 x = 1w1;
             else 
-                if (s1 == s2) 
+                if (true && s1.a == s2.a && (!s1.h.isValid() && !s2.h.isValid() || s1.h.isValid() && s2.h.isValid() && s1.h.a == s2.h.a && s1.h.b == s2.h.b)) 
                     x = 1w1;
                 else 
-                    if (a1 == a2) 
+                    if (true && (!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
                         x = 1w1;
                     else 
                         x = 1w0;
