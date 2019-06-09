--- before_pass
+++ after_pass
@@ -60,7 +60,10 @@ control ingress(inout parsed_packet_t h,
     apply {
         tns_0.apply();
         local_metadata.col.bvh.row.alt0.valid = 1w0;
-        local_metadata.row0.alt0 = local_metadata.row1.alt1;
+        {
+            local_metadata.row0.alt0.valid = local_metadata.row1.alt1.valid;
+            local_metadata.row0.alt0.port = local_metadata.row1.alt1.port;
+        }
         local_metadata.row1.alt0.valid = 1w1;
         local_metadata.row1.alt1.port = local_metadata.row0.alt1.port + 7w1;
         clone3<row_t>(CloneType.I2E, 32w0, local_metadata.row0);
