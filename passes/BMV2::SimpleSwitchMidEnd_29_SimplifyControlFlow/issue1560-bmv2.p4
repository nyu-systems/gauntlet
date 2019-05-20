*** dumps/p4_16_samples/issue1560-bmv2.p4/pruned/issue1560-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 16:58:48.945046000 +0200
--- dumps/p4_16_samples/issue1560-bmv2.p4/pruned/issue1560-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 16:58:49.000396100 +0200
*************** parser parserI(packet_in pkt, out header
*** 71,84 ****
          }
      }
      state parse_ipv4 {
!         {
!             tmp = pkt.lookahead<bit<8>>();
!             tmp_4.setValid();
!             {
!                 tmp_4.version = tmp[7:4];
!                 tmp_4.ihl = tmp[3:0];
!             }
!         }
          tmp_5 = (bit<9>)tmp_4.ihl << 2;
          tmp_6 = tmp_5 + 9w492;
          tmp_7 = tmp_6 << 3;
--- 71,80 ----
          }
      }
      state parse_ipv4 {
!         tmp = pkt.lookahead<bit<8>>();
!         tmp_4.setValid();
!         tmp_4.version = tmp[7:4];
!         tmp_4.ihl = tmp[3:0];
          tmp_5 = (bit<9>)tmp_4.ihl << 2;
          tmp_6 = tmp_5 + 9w492;
          tmp_7 = tmp_6 << 3;
