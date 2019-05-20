*** dumps/p4_16_samples/psa-example-counters-bmv2.p4/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:05.480644700 +0200
--- dumps/p4_16_samples/psa-example-counters-bmv2.p4/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_4_ConvertEnums.p4	2019-05-20 17:00:05.484429900 +0200
*************** control ingress(inout headers hdr, inout
*** 89,96 ****
      psa_ingress_output_metadata_t meta_0;
      PortId_t egress_port_0;
      psa_ingress_output_metadata_t meta_1;
!     @name("ingress.port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, PSA_CounterType_t.BYTES) port_bytes_in;
!     @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(PSA_CounterType_t.PACKETS_AND_BYTES) per_prefix_pkt_byte_count;
      @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
          per_prefix_pkt_byte_count.count();
          {
--- 89,96 ----
      psa_ingress_output_metadata_t meta_0;
      PortId_t egress_port_0;
      psa_ingress_output_metadata_t meta_1;
!     @name("ingress.port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, 32w1) port_bytes_in;
!     @name("ingress.per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(32w2) per_prefix_pkt_byte_count;
      @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
          per_prefix_pkt_byte_count.count();
          {
*************** control ingress(inout headers hdr, inout
*** 128,134 ****
      }
  }
  control egress(inout headers hdr, inout metadata user_meta, in psa_egress_input_metadata_t istd, inout psa_egress_output_metadata_t ostd) {
!     @name("egress.port_bytes_out") Counter<ByteCounter_t, PortId_t>(32w512, PSA_CounterType_t.BYTES) port_bytes_out;
      apply {
          port_bytes_out.count(istd.egress_port);
      }
--- 128,134 ----
      }
  }
  control egress(inout headers hdr, inout metadata user_meta, in psa_egress_input_metadata_t istd, inout psa_egress_output_metadata_t ostd) {
!     @name("egress.port_bytes_out") Counter<ByteCounter_t, PortId_t>(32w512, 32w1) port_bytes_out;
      apply {
          port_bytes_out.count(istd.egress_port);
      }
