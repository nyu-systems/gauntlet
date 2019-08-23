--- before_pass
+++ after_pass
@@ -22,6 +22,8 @@ parser IngressParserImpl(packet_in pkt,
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
     psa_ingress_output_metadata_t meta_1;
     PortId_t egress_port_1;
+    psa_ingress_output_metadata_t meta_2;
+    PortId_t egress_port_2;
     @name(".send_to_port") action send_to_port() {
         {
             meta_1.class_of_service = ostd.class_of_service;
@@ -46,8 +48,6 @@ control cIngress(inout headers_t hdr, in
             ostd.egress_port = meta_1.egress_port;
         }
     }
-    psa_ingress_output_metadata_t meta_2;
-    PortId_t egress_port_2;
     @name(".send_to_port") action send_to_port_0() {
         {
             meta_2.class_of_service = ostd.class_of_service;
