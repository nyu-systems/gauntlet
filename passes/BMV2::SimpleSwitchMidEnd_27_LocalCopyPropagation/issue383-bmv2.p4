--- before_pass
+++ after_pass
@@ -75,7 +75,7 @@ control ingress(inout parsed_packet_t h,
         }
         local_metadata._row1_alt0_valid4 = 1w1;
         local_metadata._row1_alt1_port7 = local_metadata._row0_alt1_port3 + 7w1;
-        clone3<row_t>(CloneType.I2E, 32w0, row_t {alt0 = alt_t {valid = local_metadata._row0_alt0_valid0,port = local_metadata._row0_alt0_port1},alt1 = alt_t {valid = local_metadata._row0_alt1_valid2,port = local_metadata._row0_alt1_port3}});
+        clone3<row_t>(CloneType.I2E, 32w0, row_t {alt0 = alt_t {valid = local_metadata._row1_alt1_valid6,port = local_metadata._row0_alt0_port1},alt1 = alt_t {valid = local_metadata._row0_alt1_valid2,port = local_metadata._row0_alt1_port3}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
