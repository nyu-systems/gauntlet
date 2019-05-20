*** dumps/p4_16_samples/issue655-bmv2.p4/pruned/issue655-bmv2-BMV2::SimpleSwitchMidEnd_15_StrengthReduction.p4	2019-05-20 16:59:35.681151400 +0200
--- dumps/p4_16_samples/issue655-bmv2.p4/pruned/issue655-bmv2-BMV2::SimpleSwitchMidEnd_16_EliminateTuples.p4	2019-05-20 16:59:35.683481700 +0200
*************** control cEgress(inout Parsed_packet hdr,
*** 29,42 ****
      apply {
      }
  }
  control vc(inout Parsed_packet hdr, inout Metadata meta) {
      apply {
!         verify_checksum<tuple<bit<16>>, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
      }
  }
  control uc(inout Parsed_packet hdr, inout Metadata meta) {
      apply {
!         update_checksum<tuple<bit<16>>, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
      }
  }
  V1Switch<Parsed_packet, Metadata>(parserI(), vc(), cIngress(), cEgress(), uc(), DeparserI()) main;
--- 29,45 ----
      apply {
      }
  }
+ struct tuple_0 {
+     bit<16> field;
+ }
  control vc(inout Parsed_packet hdr, inout Metadata meta) {
      apply {
!         verify_checksum<tuple_0, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
      }
  }
  control uc(inout Parsed_packet hdr, inout Metadata meta) {
      apply {
!         update_checksum<tuple_0, bit<16>>(true, { hdr.h.d }, hdr.h.c, HashAlgorithm.csum16);
      }
  }
  V1Switch<Parsed_packet, Metadata>(parserI(), vc(), cIngress(), cEgress(), uc(), DeparserI()) main;
