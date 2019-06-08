--- dumps/pruned/issue447-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:32:30.765398500 +0200
+++ dumps/pruned/issue447-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:32:30.829113300 +0200
@@ -10,9 +10,7 @@ struct Metadata {
 }
 control DeparserI(packet_out packet, in Parsed_packet hdr) {
     apply {
-        {
-            packet.emit<H>(hdr.h);
-        }
+        packet.emit<H>(hdr.h);
     }
 }
 parser parserI(packet_in pkt, out Parsed_packet hdr, inout Metadata meta, inout standard_metadata_t stdmeta) {
