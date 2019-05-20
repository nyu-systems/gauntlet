*** dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:06.701652700 +0200
--- dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:06.819405800 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 41,47 ****
      state start {
          parsed_hdr_2.ethernet.setInvalid();
          parsed_hdr_2.ipv4.setInvalid();
!         meta_0 = meta;
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
          transition select(parsed_hdr_2.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
--- 41,53 ----
      state start {
          parsed_hdr_2.ethernet.setInvalid();
          parsed_hdr_2.ipv4.setInvalid();
!         {
!             meta_0.send_mac_learn_msg = meta.send_mac_learn_msg;
!             {
!                 meta_0.mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
!                 meta_0.mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
!             }
!         }
          buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
          transition select(parsed_hdr_2.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
*************** parser IngressParserImpl(packet_in buffe
*** 53,60 ****
          transition start_0;
      }
      state start_0 {
!         parsed_hdr = parsed_hdr_2;
!         meta = meta_0;
          transition accept;
      }
  }
--- 59,76 ----
          transition start_0;
      }
      state start_0 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_2.ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_2.ipv4;
!             parsed_hdr.type = parsed_hdr_2.type;
!         }
!         {
!             meta.send_mac_learn_msg = meta_0.send_mac_learn_msg;
!             {
!                 meta.mac_learn_msg.srcAddr = meta_0.mac_learn_msg.srcAddr;
!                 meta.mac_learn_msg.ingress_port = meta_0.mac_learn_msg.ingress_port;
!             }
!         }
          transition accept;
      }
  }
*************** parser EgressParserImpl(packet_in buffer
*** 64,70 ****
      state start {
          parsed_hdr_3.ethernet.setInvalid();
          parsed_hdr_3.ipv4.setInvalid();
!         meta_5 = meta;
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
          transition select(parsed_hdr_3.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
--- 80,92 ----
      state start {
          parsed_hdr_3.ethernet.setInvalid();
          parsed_hdr_3.ipv4.setInvalid();
!         {
!             meta_5.send_mac_learn_msg = meta.send_mac_learn_msg;
!             {
!                 meta_5.mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
!                 meta_5.mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
!             }
!         }
          buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
          transition select(parsed_hdr_3.ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
*************** parser EgressParserImpl(packet_in buffer
*** 76,83 ****
          transition start_1;
      }
      state start_1 {
!         parsed_hdr = parsed_hdr_3;
!         meta = meta_5;
          transition accept;
      }
  }
--- 98,115 ----
          transition start_1;
      }
      state start_1 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_3.ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_3.ipv4;
!             parsed_hdr.type = parsed_hdr_3.type;
!         }
!         {
!             meta.send_mac_learn_msg = meta_5.send_mac_learn_msg;
!             {
!                 meta.mac_learn_msg.srcAddr = meta_5.mac_learn_msg.srcAddr;
!                 meta.mac_learn_msg.ingress_port = meta_5.mac_learn_msg.ingress_port;
!             }
!         }
          transition accept;
      }
  }
*************** control ingress(inout headers hdr, inout
*** 109,130 ****
      }
      @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
          {
!             meta_6 = ostd;
              egress_port_0 = egress_port;
              meta_6.drop = false;
              meta_6.multicast_group = 10w0;
              meta_6.egress_port = egress_port_0;
!             ostd = meta_6;
          }
      }
      @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
          {
!             meta_7 = ostd;
              egress_port_3 = egress_port;
              meta_7.drop = false;
              meta_7.multicast_group = 10w0;
              meta_7.egress_port = egress_port_3;
!             ostd = meta_7;
          }
      }
      @name("ingress.l2_tbl") table l2_tbl {
--- 141,194 ----
      }
      @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
          {
!             {
!                 meta_6.class_of_service = ostd.class_of_service;
!                 meta_6.clone = ostd.clone;
!                 meta_6.clone_session_id = ostd.clone_session_id;
!                 meta_6.drop = ostd.drop;
!                 meta_6.resubmit = ostd.resubmit;
!                 meta_6.multicast_group = ostd.multicast_group;
!                 meta_6.egress_port = ostd.egress_port;
!             }
              egress_port_0 = egress_port;
              meta_6.drop = false;
              meta_6.multicast_group = 10w0;
              meta_6.egress_port = egress_port_0;
!             {
!                 ostd.class_of_service = meta_6.class_of_service;
!                 ostd.clone = meta_6.clone;
!                 ostd.clone_session_id = meta_6.clone_session_id;
!                 ostd.drop = meta_6.drop;
!                 ostd.resubmit = meta_6.resubmit;
!                 ostd.multicast_group = meta_6.multicast_group;
!                 ostd.egress_port = meta_6.egress_port;
!             }
          }
      }
      @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
          {
!             {
!                 meta_7.class_of_service = ostd.class_of_service;
!                 meta_7.clone = ostd.clone;
!                 meta_7.clone_session_id = ostd.clone_session_id;
!                 meta_7.drop = ostd.drop;
!                 meta_7.resubmit = ostd.resubmit;
!                 meta_7.multicast_group = ostd.multicast_group;
!                 meta_7.egress_port = ostd.egress_port;
!             }
              egress_port_3 = egress_port;
              meta_7.drop = false;
              meta_7.multicast_group = 10w0;
              meta_7.egress_port = egress_port_3;
!             {
!                 ostd.class_of_service = meta_7.class_of_service;
!                 ostd.clone = meta_7.clone;
!                 ostd.clone_session_id = meta_7.clone_session_id;
!                 ostd.drop = meta_7.drop;
!                 ostd.resubmit = meta_7.resubmit;
!                 ostd.multicast_group = meta_7.multicast_group;
!                 ostd.egress_port = meta_7.egress_port;
!             }
          }
      }
      @name("ingress.l2_tbl") table l2_tbl {
