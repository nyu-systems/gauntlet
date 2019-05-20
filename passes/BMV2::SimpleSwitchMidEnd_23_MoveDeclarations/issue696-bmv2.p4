*** dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:25.549042800 +0200
--- dumps/p4_16_samples/issue696-bmv2.p4/pruned/issue696-bmv2-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:25.552967700 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 55,69 ****
      bit<32> inc;
      bit<32> tmp_1;
      bit<32> tmp_2;
      @name("Eg.test") action test_0() {
          {
              val.field1 = 32w0;
          }
          _pred = val.field1 != 32w0;
          {
-             bool cond;
              {
-                 bool pred;
                  cond = _pred;
                  pred = cond;
                  tmp_1 = (pred ? 32w1 : tmp_1);
--- 55,71 ----
      bit<32> inc;
      bit<32> tmp_1;
      bit<32> tmp_2;
+     bool cond;
+     bool pred;
+     bool cond_0;
+     bool pred_0;
      @name("Eg.test") action test_0() {
          {
              val.field1 = 32w0;
          }
          _pred = val.field1 != 32w0;
          {
              {
                  cond = _pred;
                  pred = cond;
                  tmp_1 = (pred ? 32w1 : tmp_1);
*************** control Eg(inout Headers hdrs, inout Met
*** 74,82 ****
          }
          inc = tmp_1;
          {
-             bool cond_0;
              {
-                 bool pred_0;
                  cond_0 = _pred;
                  pred_0 = cond_0;
                  tmp_2 = (pred_0 ? 32w1 : tmp_2);
--- 76,82 ----
