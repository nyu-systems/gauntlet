--- before_pass
+++ after_pass
@@ -86,13 +86,16 @@ parser EgressParserImpl(packet_in buffer
     }
 }
 control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
+    psa_ingress_output_metadata_t meta_0;
+    PortId_t egress_port_0;
+    psa_ingress_output_metadata_t meta_1;
     @name("ingress.port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, PSA_CounterType_t.BYTES) port_bytes_in;
     @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(PSA_CounterType_t.PACKETS_AND_BYTES) per_prefix_pkt_byte_count;
     @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
         per_prefix_pkt_byte_count.count();
         {
-            psa_ingress_output_metadata_t meta_0 = ostd;
-            PortId_t egress_port_0 = oport;
+            meta_0 = ostd;
+            egress_port_0 = oport;
             meta_0.drop = false;
             meta_0.multicast_group = 10w0;
             meta_0.egress_port = egress_port_0;
@@ -102,7 +105,7 @@ control ingress(inout headers hdr, inout
     @name("ingress.default_route_drop") action default_route_drop_0() {
         per_prefix_pkt_byte_count.count();
         {
-            psa_ingress_output_metadata_t meta_1 = ostd;
+            meta_1 = ostd;
             meta_1.drop = true;
             ostd = meta_1;
         }
