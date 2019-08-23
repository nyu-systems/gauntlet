--- before_pass
+++ after_pass
@@ -21,16 +21,12 @@ parser IngressParserImpl(packet_in pkt,
 }
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
     @name(".send_to_port") action send_to_port() {
-        {
-            ostd.drop = false;
-            ostd.multicast_group = 32w0;
-            ostd.egress_port = (PortIdUint_t)hdr.ethernet.dstAddr;
-        }
+        ostd.drop = false;
+        ostd.multicast_group = 32w0;
+        ostd.egress_port = (PortIdUint_t)hdr.ethernet.dstAddr;
     }
     @name(".ingress_drop") action ingress_drop() {
-        {
-            ostd.drop = true;
-        }
+        ostd.drop = true;
     }
     apply {
         send_to_port();
