--- before_pass
+++ after_pass
@@ -10,7 +10,9 @@ struct Metadata {
 }
 control DeparserI(packet_out packet, in Parsed_packet hdr) {
     apply {
-        packet.emit<Parsed_packet>(hdr);
+        {
+            packet.emit<H>(hdr.h);
+        }
     }
 }
 parser parserI(packet_in pkt, out Parsed_packet hdr, inout Metadata meta, inout standard_metadata_t stdmeta) {
