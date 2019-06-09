--- before_pass
+++ after_pass
@@ -8,9 +8,8 @@ struct headers {
 struct metadata {
 }
 parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
-    bit<64> tmp;
     state start {
-        tmp = packet.lookahead<bit<64>>();
+        packet.lookahead<bit<64>>();
         transition accept;
     }
 }
