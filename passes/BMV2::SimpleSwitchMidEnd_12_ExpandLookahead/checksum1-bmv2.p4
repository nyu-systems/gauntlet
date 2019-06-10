--- before_pass
+++ after_pass
@@ -61,6 +61,7 @@ parser parserI(packet_in pkt, out header
     bit<9> tmp_1;
     bit<9> tmp_2;
     bit<32> tmp_3;
+    bit<8> tmp_4;
     state start {
         pkt.extract<ethernet_t>(hdr.ethernet);
         transition select(hdr.ethernet.etherType) {
@@ -69,7 +70,11 @@ parser parserI(packet_in pkt, out header
         }
     }
     state parse_ipv4 {
-        tmp = pkt.lookahead<IPv4_up_to_ihl_only_h>();
+        {
+            tmp_4 = pkt.lookahead<bit<8>>();
+            tmp.setValid();
+            tmp = IPv4_up_to_ihl_only_h {version = tmp_4[7:4],ihl = tmp_4[3:0]};
+        }
         tmp_0 = (bit<9>)tmp.ihl << 2;
         tmp_1 = tmp_0 + 9w492;
         tmp_2 = tmp_1 << 3;
