*** dumps/p4_16_samples/parser_error-bmv2.p4/pruned/parser_error-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:54.810253900 +0200
--- dumps/p4_16_samples/parser_error-bmv2.p4/pruned/parser_error-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:54.812698200 +0200
*************** control egress(inout parsed_packet_t hdr
*** 32,38 ****
  }
  control deparser(packet_out b, in parsed_packet_t hdr) {
      apply {
!         b.emit<parsed_packet_t>(hdr);
      }
  }
  control verify_checks(inout parsed_packet_t hdr, inout local_metadata_t local_metadata) {
--- 32,40 ----
  }
  control deparser(packet_out b, in parsed_packet_t hdr) {
      apply {
!         {
!             b.emit<Ethernet>(hdr.eth);
!         }
      }
  }
  control verify_checks(inout parsed_packet_t hdr, inout local_metadata_t local_metadata) {
