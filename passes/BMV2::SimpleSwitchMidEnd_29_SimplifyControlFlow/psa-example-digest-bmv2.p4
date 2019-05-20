*** dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-05-20 17:00:06.869999300 +0200
--- dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-05-20 17:00:06.874027700 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 44,56 ****
      state start {
          parsed_hdr_2_ethernet.setInvalid();
          parsed_hdr_2_ipv4.setInvalid();
!         {
!             meta_0_send_mac_learn_msg = meta.send_mac_learn_msg;
!             {
!                 meta_0_mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
!                 meta_0_mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
!             }
!         }
          buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
          transition select(parsed_hdr_2_ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
--- 44,52 ----
      state start {
          parsed_hdr_2_ethernet.setInvalid();
          parsed_hdr_2_ipv4.setInvalid();
!         meta_0_send_mac_learn_msg = meta.send_mac_learn_msg;
!         meta_0_mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
!         meta_0_mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
          buffer.extract<ethernet_t>(parsed_hdr_2_ethernet);
          transition select(parsed_hdr_2_ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4;
*************** parser IngressParserImpl(packet_in buffe
*** 62,79 ****
          transition start_0;
      }
      state start_0 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_2_ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
!             parsed_hdr.type = parsed_hdr_2_type;
!         }
!         {
!             meta.send_mac_learn_msg = meta_0_send_mac_learn_msg;
!             {
!                 meta.mac_learn_msg.srcAddr = meta_0_mac_learn_msg.srcAddr;
!                 meta.mac_learn_msg.ingress_port = meta_0_mac_learn_msg.ingress_port;
!             }
!         }
          transition accept;
      }
  }
--- 58,69 ----
          transition start_0;
      }
      state start_0 {
!         parsed_hdr.ethernet = parsed_hdr_2_ethernet;
!         parsed_hdr.ipv4 = parsed_hdr_2_ipv4;
!         parsed_hdr.type = parsed_hdr_2_type;
!         meta.send_mac_learn_msg = meta_0_send_mac_learn_msg;
!         meta.mac_learn_msg.srcAddr = meta_0_mac_learn_msg.srcAddr;
!         meta.mac_learn_msg.ingress_port = meta_0_mac_learn_msg.ingress_port;
          transition accept;
      }
  }
*************** parser EgressParserImpl(packet_in buffer
*** 86,98 ****
      state start {
          parsed_hdr_3_ethernet.setInvalid();
          parsed_hdr_3_ipv4.setInvalid();
!         {
!             meta_5_send_mac_learn_msg = meta.send_mac_learn_msg;
!             {
!                 meta_5_mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
!                 meta_5_mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
!             }
!         }
          buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
          transition select(parsed_hdr_3_ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
--- 76,84 ----
      state start {
          parsed_hdr_3_ethernet.setInvalid();
          parsed_hdr_3_ipv4.setInvalid();
!         meta_5_send_mac_learn_msg = meta.send_mac_learn_msg;
!         meta_5_mac_learn_msg.srcAddr = meta.mac_learn_msg.srcAddr;
!         meta_5_mac_learn_msg.ingress_port = meta.mac_learn_msg.ingress_port;
          buffer.extract<ethernet_t>(parsed_hdr_3_ethernet);
          transition select(parsed_hdr_3_ethernet.etherType) {
              16w0x800: CommonParser_parse_ipv4_0;
*************** parser EgressParserImpl(packet_in buffer
*** 104,121 ****
          transition start_1;
      }
      state start_1 {
!         {
!             parsed_hdr.ethernet = parsed_hdr_3_ethernet;
!             parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
!             parsed_hdr.type = parsed_hdr_3_type;
!         }
!         {
!             meta.send_mac_learn_msg = meta_5_send_mac_learn_msg;
!             {
!                 meta.mac_learn_msg.srcAddr = meta_5_mac_learn_msg.srcAddr;
!                 meta.mac_learn_msg.ingress_port = meta_5_mac_learn_msg.ingress_port;
!             }
!         }
          transition accept;
      }
  }
--- 90,101 ----
          transition start_1;
      }
      state start_1 {
!         parsed_hdr.ethernet = parsed_hdr_3_ethernet;
!         parsed_hdr.ipv4 = parsed_hdr_3_ipv4;
!         parsed_hdr.type = parsed_hdr_3_type;
!         meta.send_mac_learn_msg = meta_5_send_mac_learn_msg;
!         meta.mac_learn_msg.srcAddr = meta_5_mac_learn_msg.srcAddr;
!         meta.mac_learn_msg.ingress_port = meta_5_mac_learn_msg.ingress_port;
          transition accept;
      }
  }
*************** control ingress(inout headers hdr, inout
*** 142,167 ****
          default_action = unknown_source_0();
      }
      @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
!         {
!             {
!             }
!             {
!                 ostd.drop = false;
!                 ostd.multicast_group = 10w0;
!                 ostd.egress_port = egress_port;
!             }
!         }
      }
      @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
!         {
!             {
!             }
!             {
!                 ostd.drop = false;
!                 ostd.multicast_group = 10w0;
!                 ostd.egress_port = egress_port;
!             }
!         }
      }
      @name("ingress.l2_tbl") table l2_tbl {
          key = {
--- 122,135 ----
          default_action = unknown_source_0();
      }
      @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
!         ostd.drop = false;
!         ostd.multicast_group = 10w0;
!         ostd.egress_port = egress_port;
      }
      @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
!         ostd.drop = false;
!         ostd.multicast_group = 10w0;
!         ostd.egress_port = egress_port;
      }
      @name("ingress.l2_tbl") table l2_tbl {
          key = {
