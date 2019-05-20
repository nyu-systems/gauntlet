*** dumps/p4_16_samples/issue1025-bmv2.p4/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:56.465019800 +0200
--- dumps/p4_16_samples/issue1025-bmv2.p4/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:56.521141500 +0200
*************** parser parserI(packet_in pkt, out header
*** 63,76 ****
          }
      }
      state parse_ipv4 {
!         {
!             tmp = pkt.lookahead<bit<8>>();
!             tmp_2.setValid();
!             {
!                 tmp_2.version = tmp[7:4];
!                 tmp_2.ihl = tmp[3:0];
!             }
!         }
          tmp_3 = (bit<9>)tmp_2.ihl << 3;
          tmp_4 = (bit<32>)tmp_3;
          pkt.extract<ipv4_t>(hdr.ipv4, tmp_4);
--- 63,72 ----
          }
      }
      state parse_ipv4 {
!         tmp = pkt.lookahead<bit<8>>();
!         tmp_2.setValid();
!         tmp_2.version = tmp[7:4];
!         tmp_2.ihl = tmp[3:0];
          tmp_3 = (bit<9>)tmp_2.ihl << 3;
          tmp_4 = (bit<32>)tmp_3;
          pkt.extract<ipv4_t>(hdr.ipv4, tmp_4);
