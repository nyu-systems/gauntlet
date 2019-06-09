--- before_pass
+++ after_pass
@@ -52,8 +52,6 @@ struct metadata {
 }
 parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     IPv4_up_to_ihl_only_h tmp;
-    bit<9> tmp_0;
-    bit<32> tmp_1;
     bit<8> tmp_2;
     state start {
         pkt.extract<ethernet_t>(hdr.ethernet);
@@ -71,9 +69,7 @@ parser parserI(packet_in pkt, out header
                 tmp.ihl = tmp_2[3:0];
             }
         }
-        tmp_0 = (bit<9>)tmp.ihl << 3;
-        tmp_1 = (bit<32>)tmp_0;
-        pkt.extract<ipv4_t>(hdr.ipv4, tmp_1);
+        pkt.extract<ipv4_t>(hdr.ipv4, (bit<32>)((bit<9>)tmp_2[3:0] << 3));
         transition select(hdr.ipv4.protocol) {
             8w6: parse_tcp;
             default: accept;
