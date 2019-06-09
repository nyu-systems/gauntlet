--- before_pass
+++ after_pass
@@ -29,7 +29,7 @@ control ingress(inout parsed_packet_t hd
         }
         local_metadata._row_alt0_valid0 = 1w1;
         local_metadata._row_alt1_port3 = local_metadata._row_alt1_port3 + 7w1;
-        clone3<row_t>(CloneType.I2E, 32w0, {{local_metadata._row_alt0_valid0,local_metadata._row_alt0_port1},{local_metadata._row_alt1_valid2,local_metadata._row_alt1_port3}});
+        clone3<row_t>(CloneType.I2E, 32w0, {{1w1,local_metadata._row_alt0_port1},{local_metadata._row_alt1_valid2,local_metadata._row_alt1_port3}});
     }
 }
 control egress(inout parsed_packet_t hdr, inout local_metadata_t local_metadata, inout standard_metadata_t standard_metadata) {
