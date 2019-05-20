*** dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:25.559118100 +0200
--- dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:59:25.563709200 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 60,74 ****
          }
          {
              {
!                 tmp_1 = (32w0 != 32w0 ? 32w1 : tmp_1);
!                 tmp_1 = (!(32w0 != 32w0) ? 32w0 : tmp_1);
              }
          }
          inc = tmp_1;
          {
              {
!                 tmp_2 = (32w0 != 32w0 ? 32w1 : tmp_2);
!                 tmp_2 = (!(32w0 != 32w0) ? 32w0 : tmp_2);
              }
          }
          debug.write(32w0, tmp_2);
--- 60,74 ----
          }
          {
              {
!                 tmp_1 = tmp_1;
!                 tmp_1 = 32w0;
              }
          }
          inc = tmp_1;
          {
              {
!                 tmp_2 = tmp_2;
!                 tmp_2 = 32w0;
              }
          }
          debug.write(32w0, tmp_2);
