--- dumps/pruned/parser_error-bmv2-BMV2::SimpleSwitchMidEnd_12_ExpandLookahead.p4	2019-06-08 18:33:05.264625900 +0200
+++ dumps/pruned/parser_error-bmv2-BMV2::SimpleSwitchMidEnd_13_ExpandEmit.p4	2019-06-08 18:33:05.266401800 +0200
@@ -32,7 +32,9 @@ control egress(inout parsed_packet_t hdr
 }
 control deparser(packet_out b, in parsed_packet_t hdr) {
     apply {
-        b.emit<parsed_packet_t>(hdr);
+        {
+            b.emit<Ethernet>(hdr.eth);
+        }
     }
 }
 control verify_checks(inout parsed_packet_t hdr, inout local_metadata_t local_metadata) {
