--- before_pass
+++ after_pass
@@ -22,7 +22,7 @@ parser IngressParserImpl(packet_in pkt,
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
     @name(".send_to_port") action send_to_port(inout psa_ingress_output_metadata_t meta_1, in PortId_t egress_port_1) {
         meta_1.drop = false;
-        meta_1.multicast_group = (MulticastGroup_t)32w0;
+        meta_1.multicast_group = 32w0;
         meta_1.egress_port = egress_port_1;
     }
     @name("cIngress.resubmit") action resubmit_1() {
@@ -38,7 +38,7 @@ control cIngress(inout headers_t hdr, in
         if (istd.packet_path != PSA_PacketPath_t.RESUBMIT) 
             resubmit_1();
         else 
-            send_to_port(ostd, (PortId_t)(PortIdUint_t)hdr.ethernet.dstAddr);
+            send_to_port(ostd, (PortIdUint_t)hdr.ethernet.dstAddr);
     }
 }
 parser EgressParserImpl(packet_in buffer, out headers_t hdr, inout metadata_t user_meta, in psa_egress_parser_input_metadata_t istd, in empty_metadata_t normal_meta, in empty_metadata_t clone_i2e_meta, in empty_metadata_t clone_e2e_meta) {
