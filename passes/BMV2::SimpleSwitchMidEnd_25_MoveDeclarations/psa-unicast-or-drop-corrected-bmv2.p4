--- before_pass
+++ after_pass
@@ -22,6 +22,7 @@ parser IngressParserImpl(packet_in pkt,
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
     psa_ingress_output_metadata_t meta_2;
     PortId_t egress_port_1;
+    psa_ingress_output_metadata_t meta_3;
     @name(".send_to_port") action send_to_port() {
         {
             meta_2.class_of_service = ostd.class_of_service;
@@ -46,7 +47,6 @@ control cIngress(inout headers_t hdr, in
             ostd.egress_port = meta_2.egress_port;
         }
     }
-    psa_ingress_output_metadata_t meta_3;
     @name(".ingress_drop") action ingress_drop() {
         {
             meta_3.class_of_service = ostd.class_of_service;
