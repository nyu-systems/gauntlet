*** dumps/p4_16_samples/issue430-bmv2.p4/pruned/issue430-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 16:59:12.928704200 +0200
--- dumps/p4_16_samples/issue430-bmv2.p4/pruned/issue430-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:59:12.930760600 +0200
*************** control MyVerifyChecksum(inout my_packet
*** 17,26 ****
      apply {
      }
  }
  control MyIngress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
      bit<32> x;
      apply {
!         hash<bit<32>, bit<32>, tuple<bit<32>>, bit<32>>(x, HashAlgorithm.crc32, 32w0, { p.h.f ^ 32w0xffff }, 32w65536);
      }
  }
  control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
--- 17,29 ----
      apply {
      }
  }
+ struct tuple_0 {
+     bit<32> field;
+ }
  control MyIngress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
      bit<32> x;
      apply {
!         hash<bit<32>, bit<32>, tuple_0, bit<32>>(x, HashAlgorithm.crc32, 32w0, { p.h.f ^ 32w0xffff }, 32w65536);
      }
  }
  control MyEgress(inout my_packet p, inout my_metadata m, inout standard_metadata_t s) {
