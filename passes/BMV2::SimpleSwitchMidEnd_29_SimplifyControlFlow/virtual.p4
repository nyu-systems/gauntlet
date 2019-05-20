*** dumps/p4_16_samples/virtual.p4/pruned/virtual-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:01:00.054989400 +0200
--- dumps/p4_16_samples/virtual.p4/pruned/virtual-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:01:00.109290900 +0200
*************** control c(inout bit<16> p) {
*** 15,24 ****
          }
          void g(inout data x) {
              data ix_1;
!             {
!                 ix_1.a = x.a;
!                 ix_1.b = x.b;
!             }
              if (x.a < x.b) 
                  x.a = x.a + 16w1;
              if (ix_1.a > x.b) 
--- 15,22 ----
          }
          void g(inout data x) {
              data ix_1;
!             ix_1.a = x.a;
!             ix_1.b = x.b;
              if (x.a < x.b) 
                  x.a = x.a + 16w1;
              if (ix_1.a > x.b) 
