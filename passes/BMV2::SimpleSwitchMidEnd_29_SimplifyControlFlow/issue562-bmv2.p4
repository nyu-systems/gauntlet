--- before_pass
+++ after_pass
@@ -20,10 +20,8 @@ parser parse(packet_in pk, out parsed_pa
 }
 control ingress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
     apply {
-        {
-            local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
-            local_metadata.row.alt0.port = local_metadata.row.alt1.port;
-        }
+        local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
+        local_metadata.row.alt0.port = local_metadata.row.alt1.port;
         local_metadata.row.alt0.valid = 1w1;
         local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
         clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
