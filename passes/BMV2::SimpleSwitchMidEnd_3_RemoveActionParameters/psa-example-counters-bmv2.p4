--- before_pass
+++ after_pass
@@ -76,13 +76,16 @@ parser EgressParserImpl(packet_in buffer
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
+    psa_ingress_output_metadata_t meta_2;
+    PortId_t egress_port_1;
+    psa_ingress_output_metadata_t meta_3;
     @name("ingress.port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, PSA_CounterType_t.BYTES) port_bytes_in_0;
     @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(PSA_CounterType_t.PACKETS_AND_BYTES) per_prefix_pkt_byte_count_0;
     @name("ingress.next_hop") action next_hop(PortId_t oport) {
         per_prefix_pkt_byte_count_0.count();
         {
-            psa_ingress_output_metadata_t meta_2 = ostd;
-            PortId_t egress_port_1 = oport;
+            meta_2 = ostd;
+            egress_port_1 = oport;
             meta_2.drop = false;
             meta_2.multicast_group = 32w0;
             meta_2.egress_port = egress_port_1;
@@ -92,7 +95,7 @@ control ingress(inout headers hdr, inout
     @name("ingress.default_route_drop") action default_route_drop() {
         per_prefix_pkt_byte_count_0.count();
         {
-            psa_ingress_output_metadata_t meta_3 = ostd;
+            meta_3 = ostd;
             meta_3.drop = true;
             ostd = meta_3;
         }
