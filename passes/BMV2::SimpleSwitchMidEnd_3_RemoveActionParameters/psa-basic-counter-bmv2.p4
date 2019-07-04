--- before_pass
+++ after_pass
@@ -20,10 +20,15 @@ parser IngressParserImpl(packet_in pkt,
     }
 }
 control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-    @name(".send_to_port") action send_to_port(inout psa_ingress_output_metadata_t meta_1, in PortId_t egress_port_1) {
+    psa_ingress_output_metadata_t meta_1;
+    PortId_t egress_port_1;
+    @name(".send_to_port") action send_to_port() {
+        meta_1 = ostd;
+        egress_port_1 = (PortIdUint_t)hdr.ethernet.dstAddr;
         meta_1.drop = false;
         meta_1.multicast_group = 32w0;
         meta_1.egress_port = egress_port_1;
+        ostd = meta_1;
     }
     @name("cIngress.counter") Counter<bit<10>, bit<12>>(32w1024, PSA_CounterType_t.PACKETS) counter_0;
     @name("cIngress.execute") action execute_1() {
@@ -36,7 +41,7 @@ control cIngress(inout headers_t hdr, in
         default_action = execute_1();
     }
     apply {
-        send_to_port(ostd, (PortIdUint_t)hdr.ethernet.dstAddr);
+        send_to_port();
         tbl_0.apply();
     }
 }
