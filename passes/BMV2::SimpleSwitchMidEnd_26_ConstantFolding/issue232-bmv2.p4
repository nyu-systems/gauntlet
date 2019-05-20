*** dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:02.268679100 +0200
--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:59:02.271398500 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 32,40 ****
              {
                  {
                      {
!                         val_2.field1 = (!false && 32w1 == 32w0 ? 32w0 : val_2.field1);
                      }
!                     val_2.field1 = (!false && 32w1 == 32w0 ? 32w8 : val_2.field1);
                      {
                      }
                  }
--- 32,40 ----
              {
                  {
                      {
!                         val_2.field1 = val_2.field1;
                      }
!                     val_2.field1 = val_2.field1;
                      {
                      }
                  }
