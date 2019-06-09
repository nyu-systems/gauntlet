--- before_pass
+++ after_pass
@@ -21,11 +21,9 @@ parser IngressParserImpl(packet_in pkt,
 }
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
     @name(".send_to_port") action send_to_port() {
-        {
-            ostd.drop = false;
-            ostd.multicast_group = 32w0;
-            ostd.egress_port = (PortIdUint_t)hdr.ethernet.dstAddr[1:0];
-        }
+        ostd.drop = false;
+        ostd.multicast_group = 32w0;
+        ostd.egress_port = (PortIdUint_t)hdr.ethernet.dstAddr[1:0];
     }
     @name("cIngress.counter") Counter<bit<10>, bit<12>>(32w1024, 32w0) counter_0;
     @name("cIngress.execute") action execute_1() {
