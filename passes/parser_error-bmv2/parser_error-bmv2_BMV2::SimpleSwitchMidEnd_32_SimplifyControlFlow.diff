--- before_pass
+++ after_pass
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
