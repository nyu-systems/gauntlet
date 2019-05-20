*** dumps/p4_16_samples/issue355-bmv2.p4/pruned/issue355-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:59:08.622782600 +0200
--- dumps/p4_16_samples/issue355-bmv2.p4/pruned/issue355-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:59:08.627879300 +0200
*************** parser parserI(packet_in pkt, out H hdr,
*** 20,26 ****
          {
              tmp = pkt.lookahead<bit<112>>();
              tmp_0.setValid();
!             tmp_0 = { tmp[111:64], tmp[63:16], tmp[15:0] };
          }
          transition select(tmp_0.etherType) {
              16w0x1000 &&& 16w0x1000: accept;
--- 20,30 ----
          {
              tmp = pkt.lookahead<bit<112>>();
              tmp_0.setValid();
!             {
!                 tmp_0.dstAddr = tmp[111:64];
!                 tmp_0.srcAddr = tmp[63:16];
!                 tmp_0.etherType = tmp[15:0];
!             }
          }
          transition select(tmp_0.etherType) {
              16w0x1000 &&& 16w0x1000: accept;
