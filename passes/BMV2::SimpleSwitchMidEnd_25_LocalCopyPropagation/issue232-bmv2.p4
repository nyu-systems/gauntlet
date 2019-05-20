*** dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:02.266404400 +0200
--- dumps/p4_16_samples/issue232-bmv2.p4/pruned/issue232-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:02.268679100 +0200
*************** control Ing(inout Headers headers, inout
*** 20,58 ****
      }
  }
  control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
-     Key inKey;
-     Key defaultKey;
-     bool same;
-     Value val_1;
-     bool done;
-     bool ok;
      Value val_2;
-     bool cond;
-     bool pred;
      @name("Eg.test") action test_0() {
          {
-             inKey.field1 = 32w1;
          }
          {
-             defaultKey.field1 = 32w0;
          }
-         same = inKey.field1 == defaultKey.field1;
          {
-             val_1.field1 = 32w0;
          }
-         done = false;
-         ok = !done && same;
          {
              {
-                 cond = ok;
-                 pred = cond;
                  {
                      {
!                         val_2.field1 = (pred ? val_1.field1 : val_2.field1);
                      }
!                     val_2.field1 = (pred ? 32w8 : val_2.field1);
                      {
-                         val_1.field1 = (pred ? val_2.field1 : val_1.field1);
                      }
                  }
              }
--- 20,41 ----
      }
  }
  control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
      Value val_2;
      @name("Eg.test") action test_0() {
          {
          }
          {
          }
          {
          }
          {
              {
                  {
                      {
!                         val_2.field1 = (!false && 32w1 == 32w0 ? 32w0 : val_2.field1);
                      }
!                     val_2.field1 = (!false && 32w1 == 32w0 ? 32w8 : val_2.field1);
                      {
                      }
                  }
              }
