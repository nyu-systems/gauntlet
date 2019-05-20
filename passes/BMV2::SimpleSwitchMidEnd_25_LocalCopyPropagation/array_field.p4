*** dumps/p4_16_samples/array_field.p4/pruned/array_field-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:57:54.444680000 +0200
--- dumps/p4_16_samples/array_field.p4/pruned/array_field-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:57:54.447932200 +0200
*************** extern bit<32> f(inout bit<1> x, in bit<
*** 5,20 ****
  control c(out H[2] h);
  package top(c _c);
  control my(out H[2] s) {
-     bit<32> a;
      bit<32> tmp_1;
-     bit<32> tmp_2;
      apply {
!         a = 32w0;
!         s[a].z = 1w1;
!         s[a + 32w1].z = 1w0;
!         tmp_1 = f(s[a].z, 1w0);
!         a = tmp_1;
!         tmp_2 = f(s[a].z, 1w1);
      }
  }
  top(my()) main;
--- 5,16 ----
  control c(out H[2] h);
  package top(c _c);
  control my(out H[2] s) {
      bit<32> tmp_1;
      apply {
!         s[32w0].z = 1w1;
!         s[32w0 + 32w1].z = 1w0;
!         tmp_1 = f(s[32w0].z, 1w0);
!         f(s[tmp_1].z, 1w1);
      }
  }
  top(my()) main;
