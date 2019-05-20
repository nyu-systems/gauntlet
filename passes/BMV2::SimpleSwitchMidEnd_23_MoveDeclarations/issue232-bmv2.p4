*** dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:02.261097700 +0200
--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:02.263887300 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 27,32 ****
--- 27,34 ----
      bool done;
      bool ok;
      Value val_2;
+     bool cond;
+     bool pred;
      @name("Eg.test") action test_0() {
          {
              inKey.field1 = 32w1;
*************** control Eg(inout Headers hdrs, inout Met
*** 41,49 ****
          done = false;
          ok = !done && same;
          {
-             bool cond;
              {
-                 bool pred;
                  cond = ok;
                  pred = cond;
                  {
--- 43,49 ----
