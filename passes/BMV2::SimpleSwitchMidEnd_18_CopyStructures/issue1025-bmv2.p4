*** dumps/p4_16_samples/issue1025-bmv2.p4/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:56.428912900 +0200
--- dumps/p4_16_samples/issue1025-bmv2.p4/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:56.432531900 +0200
*************** parser parserI(packet_in pkt, out header
*** 66,72 ****
          {
              tmp = pkt.lookahead<bit<8>>();
              tmp_2.setValid();
!             tmp_2 = { tmp[7:4], tmp[3:0] };
          }
          tmp_3 = (bit<9>)tmp_2.ihl << 3;
          tmp_4 = (bit<32>)tmp_3;
--- 66,75 ----
          {
              tmp = pkt.lookahead<bit<8>>();
              tmp_2.setValid();
!             {
!                 tmp_2.version = tmp[7:4];
!                 tmp_2.ihl = tmp[3:0];
!             }
          }
          tmp_3 = (bit<9>)tmp_2.ihl << 3;
          tmp_4 = (bit<32>)tmp_3;
