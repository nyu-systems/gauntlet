*** dumps/p4_16_samples/calc-ebpf.p4/pruned/calc-ebpf-BMV2::SimpleSwitchMidEnd_11_SimplifySelectCases.p4	2019-05-20 16:58:00.070041700 +0200
--- dumps/p4_16_samples/calc-ebpf.p4/pruned/calc-ebpf-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 16:58:00.074209800 +0200
*************** parser Parser(packet_in packet, out head
*** 22,27 ****
--- 22,30 ----
      p4calc_t tmp_3;
      p4calc_t tmp_4;
      p4calc_t tmp_5;
+     bit<128> tmp;
+     bit<128> tmp_0;
+     bit<128> tmp_1;
      state start {
          packet.extract<ethernet_t>(hdr.ethernet);
          transition select(hdr.ethernet.etherType) {
*************** parser Parser(packet_in packet, out head
*** 30,38 ****
          }
      }
      state check_p4calc {
!         tmp_3 = packet.lookahead<p4calc_t>();
!         tmp_4 = packet.lookahead<p4calc_t>();
!         tmp_5 = packet.lookahead<p4calc_t>();
          transition select(tmp_3.p, tmp_4.four, tmp_5.ver) {
              (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
              default: accept;
--- 33,53 ----
          }
      }
      state check_p4calc {
!         {
!             tmp = packet.lookahead<bit<128>>();
!             tmp_3.setValid();
!             tmp_3 = { tmp[127:120], tmp[119:112], tmp[111:104], tmp[103:96], tmp[95:64], tmp[63:32], tmp[31:0] };
!         }
!         {
!             tmp_0 = packet.lookahead<bit<128>>();
!             tmp_4.setValid();
!             tmp_4 = { tmp_0[127:120], tmp_0[119:112], tmp_0[111:104], tmp_0[103:96], tmp_0[95:64], tmp_0[63:32], tmp_0[31:0] };
!         }
!         {
!             tmp_1 = packet.lookahead<bit<128>>();
!             tmp_5.setValid();
!             tmp_5 = { tmp_1[127:120], tmp_1[119:112], tmp_1[111:104], tmp_1[103:96], tmp_1[95:64], tmp_1[63:32], tmp_1[31:0] };
!         }
          transition select(tmp_3.p, tmp_4.four, tmp_5.ver) {
              (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
              default: accept;
