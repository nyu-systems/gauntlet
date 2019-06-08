--- dumps/pruned/psa-portid-using-newtype2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:33:26.000787400 +0200
+++ dumps/pruned/psa-portid-using-newtype2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:33:26.003092600 +0200
@@ -115,7 +115,6 @@ parser FabricParser(packet_in packet, ou
     }
 }
 control FabricIngress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
-    PortId_t forwarding_mask_0;
     @name(".drop") action drop() {
         mark_to_drop();
     }
@@ -162,8 +161,7 @@ control FabricIngress(inout parsed_heade
         filtering_t_0.apply();
         forwarding_t_0.apply();
         standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec + 9w1;
-        forwarding_mask_0 = 9w0xf;
-        standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec & (PortIdUInt_t)forwarding_mask_0;
+        standard_metadata.egress_spec = (PortIdUInt_t)standard_metadata.egress_spec & (PortIdUInt_t)9w0xf;
     }
 }
 control FabricEgress(inout parsed_headers_t hdr, inout fabric_metadata_t fabric_metadata, inout standard_metadata_t standard_metadata) {
