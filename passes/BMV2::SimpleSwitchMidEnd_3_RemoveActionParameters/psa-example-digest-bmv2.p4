*** dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-05-20 17:00:06.704425800 +0200
--- dumps/p4_16_samples/psa-example-digest-bmv2.p4/pruned/psa-example-digest-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-05-20 17:00:06.784600300 +0200
*************** parser EgressParserImpl(packet_in buffer
*** 88,93 ****
--- 88,97 ----
      }
  }
  control ingress(inout headers hdr, inout metadata meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
+     psa_ingress_output_metadata_t meta_6;
+     PortId_t egress_port_0;
+     psa_ingress_output_metadata_t meta_7;
+     PortId_t egress_port_3;
      @name(".NoAction") action NoAction_0() {
      }
      @name(".NoAction") action NoAction_4() {
*************** control ingress(inout headers hdr, inout
*** 111,118 ****
      }
      @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
          {
!             psa_ingress_output_metadata_t meta_6 = ostd;
!             PortId_t egress_port_0 = egress_port;
              meta_6.drop = false;
              meta_6.multicast_group = 10w0;
              meta_6.egress_port = egress_port_0;
--- 115,122 ----
      }
      @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
          {
!             meta_6 = ostd;
!             egress_port_0 = egress_port;
              meta_6.drop = false;
              meta_6.multicast_group = 10w0;
              meta_6.egress_port = egress_port_0;
*************** control ingress(inout headers hdr, inout
*** 121,128 ****
      }
      @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
          {
!             psa_ingress_output_metadata_t meta_7 = ostd;
!             PortId_t egress_port_3 = egress_port;
              meta_7.drop = false;
              meta_7.multicast_group = 10w0;
              meta_7.egress_port = egress_port_3;
--- 125,132 ----
      }
      @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
          {
!             meta_7 = ostd;
!             egress_port_3 = egress_port;
              meta_7.drop = false;
              meta_7.multicast_group = 10w0;
              meta_7.egress_port = egress_port_3;
