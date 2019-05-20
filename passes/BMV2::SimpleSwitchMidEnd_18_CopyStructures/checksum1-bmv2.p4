*** dumps/p4_16_samples/checksum1-bmv2.p4/pruned/checksum1-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 16:58:02.416544800 +0200
--- dumps/p4_16_samples/checksum1-bmv2.p4/pruned/checksum1-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 16:58:02.419078700 +0200
*************** parser parserI(packet_in pkt, out header
*** 73,79 ****
          {
              tmp = pkt.lookahead<bit<8>>();
              tmp_4.setValid();
!             tmp_4 = { tmp[7:4], tmp[3:0] };
          }
          tmp_5 = (bit<9>)tmp_4.ihl << 2;
          tmp_6 = tmp_5 + 9w492;
--- 73,82 ----
          {
              tmp = pkt.lookahead<bit<8>>();
              tmp_4.setValid();
!             {
!                 tmp_4.version = tmp[7:4];
!                 tmp_4.ihl = tmp[3:0];
!             }
          }
          tmp_5 = (bit<9>)tmp_4.ihl << 2;
          tmp_6 = tmp_5 + 9w492;
