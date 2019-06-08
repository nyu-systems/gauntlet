--- dumps/pruned/issue447-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:32:30.702046500 +0200
+++ dumps/pruned/issue447-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:32:30.706262300 +0200
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
