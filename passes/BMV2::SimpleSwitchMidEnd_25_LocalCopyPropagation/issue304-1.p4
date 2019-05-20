*** dumps/p4_16_samples/issue304-1.p4/pruned/issue304-1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:05.966622000 +0200
--- dumps/p4_16_samples/issue304-1.p4/pruned/issue304-1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:05.968756700 +0200
*************** control t(inout bit<32> b) {
*** 7,25 ****
      @name("t.c1.x") X() c1_x_0 = {
          void a(inout bit<32> arg) {
              bit<32> c1_tmp_1;
-             bit<32> c1_tmp_2;
              c1_tmp_1 = this.b();
!             c1_tmp_2 = arg + c1_tmp_1;
!             arg = c1_tmp_2;
          }
      };
      @name("t.c2.x") X() c2_x_0 = {
          void a(inout bit<32> arg) {
              bit<32> c2_tmp_1;
-             bit<32> c2_tmp_2;
              c2_tmp_1 = this.b();
!             c2_tmp_2 = arg + c2_tmp_1;
!             arg = c2_tmp_2;
          }
      };
      apply {
--- 7,21 ----
      @name("t.c1.x") X() c1_x_0 = {
          void a(inout bit<32> arg) {
              bit<32> c1_tmp_1;
              c1_tmp_1 = this.b();
!             arg = arg + c1_tmp_1;
          }
      };
      @name("t.c2.x") X() c2_x_0 = {
          void a(inout bit<32> arg) {
              bit<32> c2_tmp_1;
              c2_tmp_1 = this.b();
!             arg = arg + c2_tmp_1;
          }
      };
      apply {
