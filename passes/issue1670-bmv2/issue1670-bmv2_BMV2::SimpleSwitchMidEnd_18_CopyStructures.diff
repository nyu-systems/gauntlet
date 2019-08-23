--- before_pass
+++ after_pass
@@ -19,7 +19,9 @@ parser parse(packet_in pk, out parsed_pa
 control ingress(inout parsed_packet_t h, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
     apply {
         h.mirrored_md.setValid();
-        h.mirrored_md.meta = switch_metadata_t {port = 8w0};
+        {
+            h.mirrored_md.meta.port = 8w0;
+        }
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
