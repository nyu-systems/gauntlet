*** dumps/p4_16_samples/issue134-bmv2.p4/pruned/issue134-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 16:58:43.193824600 +0200
--- dumps/p4_16_samples/issue134-bmv2.p4/pruned/issue134-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:58:43.196535700 +0200
*************** control VerifyChecksumI(inout H hdr, ino
*** 31,39 ****
      apply {
      }
  }
  control ComputeChecksumI(inout H hdr, inout M meta) {
      apply {
!         update_checksum<tuple<bit<1>>, bit<16>>(hdr.ipv4.ihl == 4w5, { 1w0 }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
      }
  }
  V1Switch<H, M>(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;
--- 31,42 ----
      apply {
      }
  }
+ struct tuple_0 {
+     bit<1> field;
+ }
  control ComputeChecksumI(inout H hdr, inout M meta) {
      apply {
!         update_checksum<tuple_0, bit<16>>(hdr.ipv4.ihl == 4w5, { 1w0 }, hdr.ipv4.hdrChecksum, HashAlgorithm.csum16);
      }
  }
  V1Switch<H, M>(ParserI(), VerifyChecksumI(), IngressI(), EgressI(), ComputeChecksumI(), DeparserI()) main;
