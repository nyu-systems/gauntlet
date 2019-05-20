*** dumps/p4_16_samples/virtual.p4/pruned/virtual-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:01:00.017521700 +0200
--- dumps/p4_16_samples/virtual.p4/pruned/virtual-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:01:00.020788100 +0200
*************** control c(inout bit<16> p) {
*** 15,21 ****
          }
          void g(inout data x) {
              data ix_1;
!             ix_1 = x;
              if (ix_1.a < ix_1.b) 
                  x.a = ix_1.a + 16w1;
              if (ix_1.a > ix_1.b) 
--- 15,24 ----
          }
          void g(inout data x) {
              data ix_1;
!             {
!                 ix_1.a = x.a;
!                 ix_1.b = x.b;
!             }
              if (ix_1.a < ix_1.b) 
                  x.a = ix_1.a + 16w1;
              if (ix_1.a > ix_1.b) 
