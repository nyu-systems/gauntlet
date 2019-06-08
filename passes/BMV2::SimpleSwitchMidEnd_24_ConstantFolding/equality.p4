--- dumps/pruned/equality-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:31:35.184323400 +0200
+++ dumps/pruned/equality-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:31:35.188086600 +0200
@@ -24,10 +24,10 @@ control c(out bit<1> x) {
             if (!h1.isValid() && !h2.isValid() || h1.isValid() && h2.isValid() && h1.a == h2.a && h1.b == h2.b) 
                 x = 1w1;
             else 
-                if (true && s1_a == s2_a && (!s1_h.isValid() && !s2_h.isValid() || s1_h.isValid() && s2_h.isValid() && s1_h.a == s2_h.a && s1_h.b == s2_h.b)) 
+                if (s1_a == s2_a && (!s1_h.isValid() && !s2_h.isValid() || s1_h.isValid() && s2_h.isValid() && s1_h.a == s2_h.a && s1_h.b == s2_h.b)) 
                     x = 1w1;
                 else 
-                    if (true && (!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
+                    if ((!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
                         x = 1w1;
                     else 
                         x = 1w0;
