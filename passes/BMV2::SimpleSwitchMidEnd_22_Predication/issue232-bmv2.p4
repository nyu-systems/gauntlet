*** dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_21_RemoveSelectBooleans.p4	2019-05-20 16:59:02.256961300 +0200
--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:02.261097700 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 40,52 ****
          }
          done = false;
          ok = !done && same;
!         if (ok) {
              {
!                 val_2.field1 = val_1.field1;
!             }
!             val_2.field1 = 32w8;
!             {
!                 val_1.field1 = val_2.field1;
              }
          }
      }
--- 40,60 ----
          }
          done = false;
          ok = !done && same;
!         {
!             bool cond;
              {
!                 bool pred;
!                 cond = ok;
!                 pred = cond;
!                 {
!                     {
!                         val_2.field1 = (pred ? val_1.field1 : val_2.field1);
!                     }
!                     val_2.field1 = (pred ? 32w8 : val_2.field1);
!                     {
!                         val_1.field1 = (pred ? val_2.field1 : val_1.field1);
!                     }
!                 }
              }
          }
      }
