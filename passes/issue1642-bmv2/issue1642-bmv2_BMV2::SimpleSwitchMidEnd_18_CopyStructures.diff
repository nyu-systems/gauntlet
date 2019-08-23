--- before_pass
+++ after_pass
@@ -26,7 +26,10 @@ control ingress(inout parsed_packet_t hd
     apply {
         local_metadata.s.setValid();
         local_metadata.s.f = 32w0;
-        local_metadata.row.alt0 = local_metadata.row.alt1;
+        {
+            local_metadata.row.alt0.valid = local_metadata.row.alt1.valid;
+            local_metadata.row.alt0.port = local_metadata.row.alt1.port;
+        }
         local_metadata.row.alt0.valid = 1w1;
         local_metadata.row.alt1.port = local_metadata.row.alt1.port + 7w1;
         clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row);
