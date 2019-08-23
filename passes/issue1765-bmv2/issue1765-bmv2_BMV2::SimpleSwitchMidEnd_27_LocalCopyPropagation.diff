--- before_pass
+++ after_pass
@@ -59,10 +59,6 @@ struct metadata {
 }
 parser parserI(packet_in pkt, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     IPv4_up_to_ihl_only_h tmp;
-    bit<9> tmp_0;
-    bit<9> tmp_1;
-    bit<9> tmp_2;
-    bit<32> tmp_3;
     bit<8> tmp_4;
     state start {
         pkt.extract<ethernet_t>(hdr.ethernet);
@@ -80,11 +76,7 @@ parser parserI(packet_in pkt, out header
                 tmp.ihl = tmp_4[3:0];
             }
         }
-        tmp_0 = (bit<9>)tmp.ihl << 2;
-        tmp_1 = tmp_0 + 9w492;
-        tmp_2 = tmp_1 << 3;
-        tmp_3 = (bit<32>)tmp_2;
-        pkt.extract<ipv4_t>(hdr.ipv4, tmp_3);
+        pkt.extract<ipv4_t>(hdr.ipv4, (bit<32>)(((bit<9>)tmp_4[3:0] << 2) + 9w492 << 3));
         verify(hdr.ipv4.version == 4w4, error.IPv4IncorrectVersion);
         verify(hdr.ipv4.ihl >= 4w5, error.IPv4HeaderTooShort);
         transition select(hdr.ipv4.protocol) {
