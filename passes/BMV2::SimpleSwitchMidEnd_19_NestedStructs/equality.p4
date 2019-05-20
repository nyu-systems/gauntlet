*** dumps/p4_16_samples/equality.p4/pruned/equality-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:16.903754700 +0200
--- dumps/p4_16_samples/equality.p4/pruned/equality-BMV2::SimpleSwitchMidEnd_19_NestedStructs.p4	2019-05-20 16:58:16.984815700 +0200
*************** control c(out bit<1> x) {
*** 11,18 ****
      varbit<32> b_1;
      H h1;
      H h2;
!     S s1;
!     S s2;
      H[2] a1;
      H[2] a2;
      apply {
--- 11,20 ----
      varbit<32> b_1;
      H h1;
      H h2;
!     bit<32> s1_a;
!     H s1_h;
!     bit<32> s2_a;
!     H s2_h;
      H[2] a1;
      H[2] a2;
      apply {
*************** control c(out bit<1> x) {
*** 22,28 ****
              if (!h1.isValid() && !h2.isValid() || h1.isValid() && h2.isValid() && h1.a == h2.a && h1.b == h2.b) 
                  x = 1w1;
              else 
!                 if (true && s1.a == s2.a && (!s1.h.isValid() && !s2.h.isValid() || s1.h.isValid() && s2.h.isValid() && s1.h.a == s2.h.a && s1.h.b == s2.h.b)) 
                      x = 1w1;
                  else 
                      if (true && (!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
--- 24,30 ----
              if (!h1.isValid() && !h2.isValid() || h1.isValid() && h2.isValid() && h1.a == h2.a && h1.b == h2.b) 
                  x = 1w1;
              else 
!                 if (true && s1_a == s2_a && (!s1_h.isValid() && !s2_h.isValid() || s1_h.isValid() && s2_h.isValid() && s1_h.a == s2_h.a && s1_h.b == s2_h.b)) 
                      x = 1w1;
                  else 
                      if (true && (!a1[0].isValid() && !a2[0].isValid() || a1[0].isValid() && a2[0].isValid() && a1[0].a == a2[0].a && a1[0].b == a2[0].b) && (!a1[1].isValid() && !a2[1].isValid() || a1[1].isValid() && a2[1].isValid() && a1[1].a == a2[1].a && a1[1].b == a2[1].b)) 
