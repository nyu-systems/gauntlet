--- before_pass
+++ after_pass
@@ -180,7 +180,7 @@ control FabricIngress(inout parsed_heade
         filtering_t.apply();
         forwarding_t.apply();
         standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec + 9w1;
-        standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec & (PortIdUInt_t)9w0xf;
+        standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec & 9w0xf;
     }
 }
 control FabricEgress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
