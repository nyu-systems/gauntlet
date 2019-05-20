*** dumps/p4_16_samples/equality.p4/pruned/equality-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:58:16.918526800 +0200
--- dumps/p4_16_samples/equality.p4/pruned/equality-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:58:16.921080200 +0200
*************** control c(out bit<1> x) {
*** 24,33 ****
              if (!h1.isValid() && !h2.isValid() || h1.isValid() && h2.isValid() && h1.a == h2.a && h1.b == h2.b) 
                  x = 1w1;
              else 
!                 if (true && s1_a == s2_a && (!s1_h.isValid() && !s2_h.isValid() || s1_h.isValid() && s2_h.isValid() && s1_h.a == s2_h.a && s1_h.b == s2_h.b)) 
                      x = 1w1;
                  else 
!                     if (true && (!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
                          x = 1w1;
                      else 
                          x = 1w0;
--- 24,33 ----
              if (!h1.isValid() && !h2.isValid() || h1.isValid() && h2.isValid() && h1.a == h2.a && h1.b == h2.b) 
                  x = 1w1;
              else 
!                 if (s1_a == s2_a && (!s1_h.isValid() && !s2_h.isValid() || s1_h.isValid() && s2_h.isValid() && s1_h.a == s2_h.a && s1_h.b == s2_h.b)) 
                      x = 1w1;
                  else 
!                     if ((!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
                          x = 1w1;
                      else 
                          x = 1w0;
