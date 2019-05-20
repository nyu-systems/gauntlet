*** dumps/p4_16_samples/rcp1.p4/pruned/rcp1-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:19.426459600 +0200
--- dumps/p4_16_samples/rcp1.p4/pruned/rcp1-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:19.428610800 +0200
*************** extern ConditionalAccumulator<T> {
*** 4,16 ****
      void read(out T value);
      void write(in T value, in bool condition);
  }
- enum CounterType {
-     packets,
-     bytes,
-     packets_and_bytes
- }
  extern Counter<T> {
!     Counter(CounterType type);
      void count();
  }
  control proto<P, M>(inout P packet, in M meta);
--- 4,11 ----
      void read(out T value);
      void write(in T value, in bool condition);
  }
  extern Counter<T> {
!     Counter(bit<32> type);
      void count();
  }
  control proto<P, M>(inout P packet, in M meta);
*************** struct Metadata {
*** 22,28 ****
      bit<32> pkt_len;
  }
  control ingress(inout H pkt_hdr, in Metadata metadata) {
!     @name("ingress.input_traffic_bytes") Counter<bit<32>>(CounterType.packets_and_bytes) input_traffic_bytes;
      @name("ingress.sum_rtt_Tr") ConditionalAccumulator<bit<32>>(32w1) sum_rtt_Tr;
      @name("ingress.num_pkts_with_rtt") ConditionalAccumulator<bit<32>>(32w1) num_pkts_with_rtt;
      apply {
--- 17,23 ----
      bit<32> pkt_len;
  }
  control ingress(inout H pkt_hdr, in Metadata metadata) {
!     @name("ingress.input_traffic_bytes") Counter<bit<32>>(32w2) input_traffic_bytes;
      @name("ingress.sum_rtt_Tr") ConditionalAccumulator<bit<32>>(32w1) sum_rtt_Tr;
      @name("ingress.num_pkts_with_rtt") ConditionalAccumulator<bit<32>>(32w1) num_pkts_with_rtt;
      apply {
