--- dumps/pruned/parser_error-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:33:05.313279200 +0200
+++ dumps/pruned/parser_error-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:33:05.320939300 +0200
@@ -32,9 +32,7 @@ control egress(inout parsed_packet_t hdr
 }
 control deparser(packet_out b, in parsed_packet_t hdr) {
     apply {
-        {
-            b.emit<Ethernet>(hdr.eth);
-        }
+        b.emit<Ethernet>(hdr.eth);
     }
 }
 control verify_checks(inout parsed_packet_t hdr, inout local_metadata_t local_metadata) {
