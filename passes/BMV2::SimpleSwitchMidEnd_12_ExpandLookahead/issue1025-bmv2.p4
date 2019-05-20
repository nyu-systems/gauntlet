--- dumps/p4_16_samples/issue1025-bmv2.p4/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_11_SimplifySelectCases.p4	2019-05-20 17:30:29.220216200 +0200
+++ dumps/p4_16_samples/issue1025-bmv2.p4/pruned/issue1025-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:30:29.223866400 +0200
@@ -54,6 +54,7 @@ parser parserI(packet_in pkt, out header
     IPv4_up_to_ihl_only_h tmp_2;
     bit<9> tmp_3;
     bit<32> tmp_4;
+    bit<8> tmp;
     state start {
         pkt.extract<ethernet_t>(hdr.ethernet);
         transition select(hdr.ethernet.etherType) {
@@ -62,7 +63,11 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_ipv4 {
-        tmp_2 = pkt.lookahead<IPv4_up_to_ihl_only_h>();
+        {
+            tmp = pkt.lookahead<bit<8>>();
+            tmp_2.setValid();
+            tmp_2 = { tmp[7:4], tmp[3:0] };
+        }
         tmp_3 = (bit<9>)tmp_2.ihl << 3;
         tmp_4 = (bit<32>)tmp_3;
         pkt.extract<ipv4_t>(hdr.ipv4, tmp_4);
