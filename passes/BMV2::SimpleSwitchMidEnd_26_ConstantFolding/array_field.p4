*** dumps/p4_16_samples/array_field.p4/pruned/array_field-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:54.447932200 +0200
--- dumps/p4_16_samples/array_field.p4/pruned/array_field-BMV2::SimpleSwitchMidEnd_26_ConstantFolding.p4	2019-05-20 16:57:54.450211100 +0200
*************** control my(out H[2] s) {
*** 8,14 ****
      bit<32> tmp_1;
      apply {
          s[32w0].z = 1w1;
!         s[32w0 + 32w1].z = 1w0;
          tmp_1 = f(s[32w0].z, 1w0);
          f(s[tmp_1].z, 1w1);
      }
--- 8,14 ----
      bit<32> tmp_1;
      apply {
          s[32w0].z = 1w1;
!         s[32w1].z = 1w0;
          tmp_1 = f(s[32w0].z, 1w0);
          f(s[tmp_1].z, 1w1);
      }
