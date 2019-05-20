*** dumps/p4_16_samples/issue355-bmv2.p4/pruned/issue355-bmv2-BMV2::SimpleSwitchMidEnd_11_SimplifySelectCases.p4	2019-05-20 16:59:08.600267900 +0200
--- dumps/p4_16_samples/issue355-bmv2.p4/pruned/issue355-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:59:08.602523900 +0200
*************** control DeparserI(packet_out packet, in
*** 15,22 ****
  }
  parser parserI(packet_in pkt, out H hdr, inout M meta, inout standard_metadata_t stdmeta) {
      ethernet_t tmp_0;
      state start {
!         tmp_0 = pkt.lookahead<ethernet_t>();
          transition select(tmp_0.etherType) {
              16w0x1000 &&& 16w0x1000: accept;
          }
--- 15,27 ----
  }
  parser parserI(packet_in pkt, out H hdr, inout M meta, inout standard_metadata_t stdmeta) {
      ethernet_t tmp_0;
+     bit<112> tmp;
      state start {
!         {
!             tmp = pkt.lookahead<bit<112>>();
!             tmp_0.setValid();
!             tmp_0 = { tmp[111:64], tmp[63:16], tmp[15:0] };
!         }
          transition select(tmp_0.etherType) {
              16w0x1000 &&& 16w0x1000: accept;
          }
