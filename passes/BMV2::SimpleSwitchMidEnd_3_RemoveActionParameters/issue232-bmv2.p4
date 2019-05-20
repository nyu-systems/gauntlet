*** dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 16:59:02.280989700 +0200
--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 16:59:02.303867400 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 26,31 ****
--- 26,32 ----
      Value val_1;
      bool done;
      bool ok;
+     Value val_2;
      @name("Eg.test") action test_0() {
          inKey = { 32w1 };
          defaultKey = { 32w0 };
*************** control Eg(inout Headers hdrs, inout Met
*** 34,40 ****
          done = false;
          ok = !done && same;
          if (ok) {
!             Value val_2 = val_1;
              val_2.field1 = 32w8;
              val_1 = val_2;
          }
--- 35,41 ----
          done = false;
          ok = !done && same;
          if (ok) {
!             val_2 = val_1;
              val_2.field1 = 32w8;
              val_1 = val_2;
          }
