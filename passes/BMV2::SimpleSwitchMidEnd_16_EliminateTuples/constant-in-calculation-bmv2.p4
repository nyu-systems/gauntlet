*** dumps/p4_16_samples/constant-in-calculation-bmv2.p4/pruned/constant-in-calculation-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 16:58:08.457192100 +0200
--- dumps/p4_16_samples/constant-in-calculation-bmv2.p4/pruned/constant-in-calculation-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:58:08.459873700 +0200
*************** control deparser(packet_out b, in Header
*** 31,39 ****
          b.emit<hdr>(h.h);
      }
  }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      apply {
!         hash<bit<16>, bit<10>, tuple<bit<16>>, bit<10>>(h.h.a, HashAlgorithm.crc16, 10w0, { 16w1 }, 10w4);
          sm.egress_spec = 9w0;
      }
  }
--- 31,42 ----
          b.emit<hdr>(h.h);
      }
  }
+ struct tuple_0 {
+     bit<16> field;
+ }
  control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
      apply {
!         hash<bit<16>, bit<10>, tuple_0, bit<10>>(h.h.a, HashAlgorithm.crc16, 10w0, { 16w1 }, 10w4);
          sm.egress_spec = 9w0;
      }
  }
