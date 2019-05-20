*** dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:47.511446600 +0200
--- dumps/p4_16_samples/mux-bmv2.p4/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:59:47.514263400 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 21,28 ****
          val = res;
          {
              {
!                 tmp_0 = (true ? res[31:0] : tmp_0);
!                 tmp_0 = (!true ? 32w1 : tmp_0);
              }
          }
          val[31:0] = tmp_0;
--- 21,28 ----
          val = res;
          {
              {
!                 tmp_0 = res[31:0];
!                 tmp_0 = tmp_0;
              }
          }
          val[31:0] = tmp_0;
