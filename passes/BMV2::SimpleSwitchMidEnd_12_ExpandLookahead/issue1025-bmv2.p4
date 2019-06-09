--- before_pass
+++ after_pass
@@ -54,6 +54,7 @@ parser parserI(packet_in pkt, out header
     IPv4_up_to_ihl_only_h tmp;
     bit<9> tmp_0;
     bit<32> tmp_1;
+    bit<8> tmp_2;
     state start {
         pkt.extract<ethernet_t>(hdr.ethernet);
         transition select(hdr.ethernet.etherType) {
@@ -62,7 +63,11 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_ipv4 {
-        tmp = pkt.lookahead<IPv4_up_to_ihl_only_h>();
+        {
+            tmp_2 = pkt.lookahead<bit<8>>();
+            tmp.setValid();
+            tmp = {tmp_2[7:4],tmp_2[3:0]};
+        }
         tmp_0 = (bit<9>)tmp.ihl << 3;
         tmp_1 = (bit<32>)tmp_0;
         pkt.extract<ipv4_t>(hdr.ipv4, tmp_1);
