--- before_pass
+++ after_pass
@@ -4,13 +4,8 @@ extern ConditionalAccumulator<T> {
     void read(out T value);
     void write(in T value, in bool condition);
 }
-enum CounterType {
-    packets,
-    bytes,
-    packets_and_bytes
-}
 extern Counter<T> {
-    Counter(CounterType type);
+    Counter(bit<32> type);
     void count();
 }
 control proto<P, M>(inout P packet, in M meta);
@@ -22,7 +17,7 @@ struct Metadata {
     bit<32> pkt_len;
 }
 control ingress(inout H pkt_hdr, in Metadata metadata) {
-    @name("ingress.input_traffic_bytes") Counter<bit<32>>(CounterType.packets_and_bytes) input_traffic_bytes;
+    @name("ingress.input_traffic_bytes") Counter<bit<32>>(32w2) input_traffic_bytes;
     @name("ingress.sum_rtt_Tr") ConditionalAccumulator<bit<32>>(32w1) sum_rtt_Tr;
     @name("ingress.num_pkts_with_rtt") ConditionalAccumulator<bit<32>>(32w1) num_pkts_with_rtt;
     apply {
