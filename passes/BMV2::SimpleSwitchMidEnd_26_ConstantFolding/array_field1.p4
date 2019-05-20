*** dumps/p4_16_samples/array_field1.p4/pruned/array_field1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:54.783250700 +0200
--- dumps/p4_16_samples/array_field1.p4/pruned/array_field1-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:57:54.785863300 +0200
*************** control my(out H[2] s) {
*** 12,18 ****
      bit<1> tmp_17;
      @name("my.act") action act_0() {
          s[32w0].z = 1w1;
!         s[32w0 + 32w1].z = 1w0;
          tmp_12 = 32w0;
          tmp_13 = s[32w0].z;
          tmp_17 = f(tmp_13, 1w0);
--- 12,18 ----
      bit<1> tmp_17;
      @name("my.act") action act_0() {
          s[32w0].z = 1w1;
!         s[32w1].z = 1w0;
          tmp_12 = 32w0;
          tmp_13 = s[32w0].z;
          tmp_17 = f(tmp_13, 1w0);
