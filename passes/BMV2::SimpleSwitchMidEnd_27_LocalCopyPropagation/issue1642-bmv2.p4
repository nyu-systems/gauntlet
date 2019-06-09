--- before_pass
+++ after_pass
@@ -35,7 +35,7 @@ control ingress(inout parsed_packet_t hd
         }
         local_metadata._row_alt0_valid1 = 1w1;
         local_metadata._row_alt1_port4 = local_metadata._row_alt1_port4 + 7w1;
-        clone3<row_t>(CloneType.I2E, 32w0, {{local_metadata._row_alt0_valid1,local_metadata._row_alt0_port2},{local_metadata._row_alt1_valid3,local_metadata._row_alt1_port4}});
+        clone3<row_t>(CloneType.I2E, 32w0, {{1w1,local_metadata._row_alt0_port2},{local_metadata._row_alt1_valid3,local_metadata._row_alt1_port4}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
