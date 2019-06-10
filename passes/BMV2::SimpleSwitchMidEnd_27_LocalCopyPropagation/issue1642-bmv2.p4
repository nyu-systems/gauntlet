--- before_pass
+++ after_pass
@@ -35,7 +35,7 @@ control ingress(inout parsed_packet_t hd
         }
         local_metadata._row_alt0_valid1 = 1w1;
         local_metadata._row_alt1_port4 = local_metadata._row_alt1_port4 + 7w1;
-        clone3<row_t>(CloneType.I2E, 32w0, row_t {alt0 = alt_t {valid = local_metadata._row_alt0_valid1,port = local_metadata._row_alt0_port2},alt1 = alt_t {valid = local_metadata._row_alt1_valid3,port = local_metadata._row_alt1_port4}});
+        clone3<row_t>(CloneType.I2E, 32w0, row_t {alt0 = alt_t {valid = 1w1,port = local_metadata._row_alt0_port2},alt1 = alt_t {valid = local_metadata._row_alt1_valid3,port = local_metadata._row_alt1_port4}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
