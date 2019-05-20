*** dumps/p4_16_samples/issue447-bmv2.p4/pruned/issue447-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:15.224009600 +0200
--- dumps/p4_16_samples/issue447-bmv2.p4/pruned/issue447-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-05-20 16:59:15.226395300 +0200
*************** struct Metadata {
*** 10,16 ****
  }
  control DeparserI(packet_out packet, in Parsed_packet hdr) {
      apply {
!         packet.emit<Parsed_packet>(hdr);
      }
  }
  parser parserI(packet_in pkt, out Parsed_packet hdr, inout Metadata meta, inout standard_metadata_t stdmeta) {
--- 10,18 ----
  }
  control DeparserI(packet_out packet, in Parsed_packet hdr) {
      apply {
!         {
!             packet.emit<H>(hdr.h);
!         }
      }
  }
  parser parserI(packet_in pkt, out Parsed_packet hdr, inout Metadata meta, inout standard_metadata_t stdmeta) {
