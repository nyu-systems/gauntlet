*** dumps/p4_16_samples/issue355-bmv2.p4/pruned/issue355-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:59:08.656777200 +0200
--- dumps/p4_16_samples/issue355-bmv2.p4/pruned/issue355-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:59:08.712632700 +0200
*************** parser parserI(packet_in pkt, out H hdr,
*** 17,31 ****
      ethernet_t tmp_0;
      bit<112> tmp;
      state start {
!         {
!             tmp = pkt.lookahead<bit<112>>();
!             tmp_0.setValid();
!             {
!                 tmp_0.dstAddr = tmp[111:64];
!                 tmp_0.srcAddr = tmp[63:16];
!                 tmp_0.etherType = tmp[15:0];
!             }
!         }
          transition select(tmp_0.etherType) {
              16w0x1000 &&& 16w0x1000: accept;
          }
--- 17,27 ----
      ethernet_t tmp_0;
      bit<112> tmp;
      state start {
!         tmp = pkt.lookahead<bit<112>>();
!         tmp_0.setValid();
!         tmp_0.dstAddr = tmp[111:64];
!         tmp_0.srcAddr = tmp[63:16];
!         tmp_0.etherType = tmp[15:0];
          transition select(tmp_0.etherType) {
              16w0x1000 &&& 16w0x1000: accept;
          }
