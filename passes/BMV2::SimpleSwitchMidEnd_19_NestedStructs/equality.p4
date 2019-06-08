--- before_pass
+++ after_pass
@@ -11,8 +11,10 @@ control c(out bit<1> x) {
     varbit<32> b_1;
     H h1;
     H h2;
-    S s1;
-    S s2;
+    bit<32> s1_a;
+    H s1_h;
+    bit<32> s2_a;
+    H s2_h;
     H[2] a1;
     H[2] a2;
     apply {
@@ -22,7 +24,7 @@ control c(out bit<1> x) {
             if (!h1.isValid() && !h2.isValid() || h1.isValid() && h2.isValid() && h1.a == h2.a && h1.b == h2.b) 
                 x = 1w1;
             else 
-                if (true && s1.a == s2.a && (!s1.h.isValid() && !s2.h.isValid() || s1.h.isValid() && s2.h.isValid() && s1.h.a == s2.h.a && s1.h.b == s2.h.b)) 
+                if (true && s1_a == s2_a && (!s1_h.isValid() && !s2_h.isValid() || s1_h.isValid() && s2_h.isValid() && s1_h.a == s2_h.a && s1_h.b == s2_h.b)) 
                     x = 1w1;
                 else 
                     if (true && (!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
