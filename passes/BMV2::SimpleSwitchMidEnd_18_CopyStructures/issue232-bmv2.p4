*** dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:59:02.246214200 +0200
--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:02.248573600 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 28,43 ****
      bool ok;
      Value val_2;
      @name("Eg.test") action test_0() {
!         inKey = { 32w1 };
!         defaultKey = { 32w0 };
          same = true && inKey.field1 == defaultKey.field1;
!         val_1 = { 32w0 };
          done = false;
          ok = !done && same;
          if (ok) {
!             val_2 = val_1;
              val_2.field1 = 32w8;
!             val_1 = val_2;
          }
      }
      apply {
--- 28,53 ----
      bool ok;
      Value val_2;
      @name("Eg.test") action test_0() {
!         {
!             inKey.field1 = 32w1;
!         }
!         {
!             defaultKey.field1 = 32w0;
!         }
          same = true && inKey.field1 == defaultKey.field1;
!         {
!             val_1.field1 = 32w0;
!         }
          done = false;
          ok = !done && same;
          if (ok) {
!             {
!                 val_2.field1 = val_1.field1;
!             }
              val_2.field1 = 32w8;
!             {
!                 val_1.field1 = val_2.field1;
!             }
          }
      }
      apply {
