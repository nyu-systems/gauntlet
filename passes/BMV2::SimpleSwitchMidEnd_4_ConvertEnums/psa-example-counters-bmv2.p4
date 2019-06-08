--- dumps/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:33:16.601277500 +0200
+++ dumps/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-06-08 18:33:16.609184300 +0200
@@ -89,8 +89,8 @@ control ingress(inout headers hdr, inout
     psa_ingress_output_metadata_t meta_0;
     PortId_t egress_port_0;
     psa_ingress_output_metadata_t meta_1;
-    @name("ingress.port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, PSA_CounterType_t.BYTES) port_bytes_in;
-    @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(PSA_CounterType_t.PACKETS_AND_BYTES) per_prefix_pkt_byte_count;
+    @name("ingress.port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, 32w1) port_bytes_in;
+    @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(32w2) per_prefix_pkt_byte_count;
     @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
         per_prefix_pkt_byte_count.count();
         {
@@ -128,7 +128,7 @@ control ingress(inout headers hdr, inout
     }
 }
 control egress(inout headers hdr, inout metadata user_meta, in psa_egress_input_metadata_t istd, inout psa_egress_output_metadata_t ostd) {
-    @name("egress.port_bytes_out") Counter<ByteCounter_t, PortId_t>(32w512, PSA_CounterType_t.BYTES) port_bytes_out;
+    @name("egress.port_bytes_out") Counter<ByteCounter_t, PortId_t>(32w512, 32w1) port_bytes_out;
     apply {
         port_bytes_out.count(istd.egress_port);
     }
