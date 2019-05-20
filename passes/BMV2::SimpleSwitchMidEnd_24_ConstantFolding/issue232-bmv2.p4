*** dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:02.263887300 +0200
--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:02.266404400 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 36,42 ****
          {
              defaultKey.field1 = 32w0;
          }
!         same = true && inKey.field1 == defaultKey.field1;
          {
              val_1.field1 = 32w0;
          }
--- 36,42 ----
          {
              defaultKey.field1 = 32w0;
          }
!         same = inKey.field1 == defaultKey.field1;
          {
              val_1.field1 = 32w0;
          }
