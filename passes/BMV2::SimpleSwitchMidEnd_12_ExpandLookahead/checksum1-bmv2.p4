--- dumps/p4_16_samples/checksum1-bmv2.p4/pruned/checksum1-bmv2-BMV2::SimpleSwitchMidEnd_11_SimplifySelectCases.p4	2019-05-20 17:29:17.881552600 +0200
+++ dumps/p4_16_samples/checksum1-bmv2.p4/pruned/checksum1-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-05-20 17:29:17.884162100 +0200
@@ -61,6 +61,7 @@ parser parserI(packet_in pkt, out header
     bit<9> tmp_6;
     bit<9> tmp_7;
     bit<32> tmp_8;
+    bit<8> tmp;
     state start {
         pkt.extract<ethernet_t>(hdr.ethernet);
         transition select(hdr.ethernet.etherType) {
@@ -69,7 +70,11 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_ipv4 {
-        tmp_4 = pkt.lookahead<IPv4_up_to_ihl_only_h>();
+        {
+            tmp = pkt.lookahead<bit<8>>();
+            tmp_4.setValid();
+            tmp_4 = { tmp[7:4], tmp[3:0] };
+        }
         tmp_5 = (bit<9>)tmp_4.ihl << 2;
         tmp_6 = tmp_5 + 9w492;
         tmp_7 = tmp_6 << 3;
