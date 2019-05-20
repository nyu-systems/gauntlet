*** dumps/p4_16_samples/issue584-1.p4/pruned/issue584-1-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 16:59:22.155732200 +0200
--- dumps/p4_16_samples/issue584-1.p4/pruned/issue584-1-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 16:59:22.158224400 +0200
*************** control p();
*** 4,13 ****
  package top(p _p);
  control c() {
      bit<16> var;
-     bit<32> hdr_1;
      apply {
!         hdr_1 = 32w0;
!         hash<bit<16>, bit<16>, bit<32>, bit<16>>(var, HashAlgorithm.crc16, 16w0, hdr_1, 16w0xffff);
      }
  }
  top(c()) main;
--- 4,11 ----
  package top(p _p);
  control c() {
      bit<16> var;
      apply {
!         hash<bit<16>, bit<16>, bit<32>, bit<16>>(var, HashAlgorithm.crc16, 16w0, 32w0, 16w0xffff);
      }
  }
  top(c()) main;
