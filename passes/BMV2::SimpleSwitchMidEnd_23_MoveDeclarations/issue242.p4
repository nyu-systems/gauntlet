*** dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:02.967810900 +0200
--- dumps/p4_16_samples/issue242.p4/pruned/issue242-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:02.970339400 +0200
*************** control Eg(inout Headers hdrs, inout Met
*** 53,58 ****
--- 53,62 ----
      bit<32> inc;
      bit<32> tmp_1;
      bit<32> tmp_2;
+     bool cond;
+     bool pred;
+     bool cond_0;
+     bool pred_0;
      @name("Eg.debug") register<bit<32>>(32w100) debug;
      @name("Eg.reg") register<bit<32>>(32w1) reg;
      @name("Eg.test") action test_0() {
*************** control Eg(inout Headers hdrs, inout Met
*** 61,69 ****
          }
          _pred = val.field1 != 32w0;
          {
-             bool cond;
              {
-                 bool pred;
                  cond = _pred;
                  pred = cond;
                  tmp_1 = (pred ? 32w1 : tmp_1);
--- 65,71 ----
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
