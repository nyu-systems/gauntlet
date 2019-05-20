*** dumps/p4_16_samples/psa-example-counters-bmv2.p4/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:05.376568600 +0200
--- dumps/p4_16_samples/psa-example-counters-bmv2.p4/pruned/psa-example-counters-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:05.517756800 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 39,45 ****
      state start {
          parsed_hdr_2.ethernet.setInvalid();
          parsed_hdr_2.ipv4.setInvalid();
!         user_meta_2 = user_meta;
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
          transition select(parsed_hdr_2.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
--- 39,48 ----
      state start {
          parsed_hdr_2.ethernet.setInvalid();
          parsed_hdr_2.ipv4.setInvalid();
!         {
!             {
!             }
!         }
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
          transition select(parsed_hdr_2.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
*************** parser IngressParserImpl(packet_in buffe
*** 51,58 ****
          transition start_0;
      }
      state start_0 {
!         parsed_hdr = parsed_hdr_2;
!         user_meta = user_meta_2;
          transition accept;
      }
  }
--- 54,67 ----
          transition start_0;
      }
      state start_0 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_2.ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
!         }
!         {
!             {
!             }
!         }
          transition accept;
      }
  }
*************** parser EgressParserImpl(packet_in buffer
*** 62,68 ****
      state start {
          parsed_hdr_3.ethernet.setInvalid();
          parsed_hdr_3.ipv4.setInvalid();
!         user_meta_3 = user_meta;
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
          transition select(parsed_hdr_3.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
--- 71,80 ----
      state start {
          parsed_hdr_3.ethernet.setInvalid();
          parsed_hdr_3.ipv4.setInvalid();
!         {
!             {
!             }
!         }
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
          transition select(parsed_hdr_3.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
*************** parser EgressParserImpl(packet_in buffer
*** 74,81 ****
          transition start_1;
      }
      state start_1 {
!         parsed_hdr = parsed_hdr_3;
!         user_meta = user_meta_3;
          transition accept;
      }
  }
--- 86,99 ----
          transition start_1;
      }
      state start_1 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_3.ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
!         }
!         {
!             {
!             }
!         }
          transition accept;
      }
  }
*************** control ingress(inout headers hdr, inout
*** 88,107 ****
      @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
          per_prefix_pkt_byte_count.count();
          {
!             meta_0 = ostd;
              egress_port_0 = oport;
              meta_0.drop = false;
              meta_0.multicast_group = 10w0;
              meta_0.egress_port = egress_port_0;
!             ostd = meta_0;
          }
      }
      @name("ingress.default_route_drop") action default_route_drop_0() {
          per_prefix_pkt_byte_count.count();
          {
!             meta_1 = ostd;
              meta_1.drop = true;
!             ostd = meta_1;
          }
      }
      @name("ingress.ipv4_da_lpm") table ipv4_da_lpm {
--- 106,157 ----
      @name("ingress.next_hop") action next_hop_0(PortId_t oport) {
          per_prefix_pkt_byte_count.count();
          {
!             {
!                 meta_0.class_of_service = ostd.class_of_service;
!                 meta_0.clone = ostd.clone;
!                 meta_0.clone_session_id = ostd.clone_session_id;
!                 meta_0.drop = ostd.drop;
!                 meta_0.resubmit = ostd.resubmit;
!                 meta_0.multicast_group = ostd.multicast_group;
!                 meta_0.egress_port = ostd.egress_port;
!             }
              egress_port_0 = oport;
              meta_0.drop = false;
              meta_0.multicast_group = 10w0;
              meta_0.egress_port = egress_port_0;
!             {
!                 ostd.class_of_service = meta_0.class_of_service;
!                 ostd.clone = meta_0.clone;
!                 ostd.clone_session_id = meta_0.clone_session_id;
!                 ostd.drop = meta_0.drop;
!                 ostd.resubmit = meta_0.resubmit;
!                 ostd.multicast_group = meta_0.multicast_group;
!                 ostd.egress_port = meta_0.egress_port;
!             }
          }
      }
      @name("ingress.default_route_drop") action default_route_drop_0() {
          per_prefix_pkt_byte_count.count();
          {
!             {
!                 meta_1.class_of_service = ostd.class_of_service;
!                 meta_1.clone = ostd.clone;
!                 meta_1.clone_session_id = ostd.clone_session_id;
!                 meta_1.drop = ostd.drop;
!                 meta_1.resubmit = ostd.resubmit;
!                 meta_1.multicast_group = ostd.multicast_group;
!                 meta_1.egress_port = ostd.egress_port;
!             }
              meta_1.drop = true;
!             {
!                 ostd.class_of_service = meta_1.class_of_service;
!                 ostd.clone = meta_1.clone;
!                 ostd.clone_session_id = meta_1.clone_session_id;
!                 ostd.drop = meta_1.drop;
!                 ostd.resubmit = meta_1.resubmit;
!                 ostd.multicast_group = meta_1.multicast_group;
!                 ostd.egress_port = meta_1.egress_port;
!             }
          }
      }
      @name("ingress.ipv4_da_lpm") table ipv4_da_lpm {
