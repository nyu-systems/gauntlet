--- before_pass
+++ after_pass
@@ -10,7 +10,7 @@ enum CounterType {
     packets_and_bytes
 }
 extern Counter<T> {
-    Counter(CounterType type);
+    Counter(bit<32> type);
     void count();
 }
 control proto<P, M>(inout P packet, in M meta);
@@ -22,7 +22,7 @@ struct Metadata {
     bit<32> pkt_len;
 }
 control ingress(inout H pkt_hdr, in Metadata metadata) {
-    @name("ingress.input_traffic_bytes") Counter<bit<32>>(CounterType.packets_and_bytes) input_traffic_bytes_0;
+    @name("ingress.input_traffic_bytes") Counter<bit<32>>(32w2) input_traffic_bytes_0;
     @name("ingress.sum_rtt_Tr") ConditionalAccumulator<bit<32>>(32w1) sum_rtt_Tr_0;
     @name("ingress.num_pkts_with_rtt") ConditionalAccumulator<bit<32>>(32w1) num_pkts_with_rtt_0;
     apply {
