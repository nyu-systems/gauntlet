*** dumps/p4_16_samples/psa-multicast-basic-bmv2.p4/pruned/psa-multicast-basic-bmv2-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:14.096790700 +0200
--- dumps/p4_16_samples/psa-multicast-basic-bmv2.p4/pruned/psa-multicast-basic-bmv2-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:14.099659500 +0200
*************** parser IngressParserImpl(packet_in pkt,
*** 20,48 ****
      }
  }
  control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-     psa_ingress_output_metadata_t meta_1;
-     MulticastGroup_t multicast_group_1;
      @name(".multicast") action multicast() {
          {
-             meta_1.class_of_service = ostd.class_of_service;
-             meta_1.clone = ostd.clone;
-             meta_1.clone_session_id = ostd.clone_session_id;
-             meta_1.drop = ostd.drop;
-             meta_1.resubmit = ostd.resubmit;
-             meta_1.multicast_group = ostd.multicast_group;
-             meta_1.egress_port = ostd.egress_port;
          }
-         multicast_group_1 = (MulticastGroup_t)hdr.ethernet.dstAddr[31:0];
-         meta_1.drop = false;
-         meta_1.multicast_group = multicast_group_1;
          {
!             ostd.class_of_service = meta_1.class_of_service;
!             ostd.clone = meta_1.clone;
!             ostd.clone_session_id = meta_1.clone_session_id;
!             ostd.drop = meta_1.drop;
!             ostd.resubmit = meta_1.resubmit;
!             ostd.multicast_group = meta_1.multicast_group;
!             ostd.egress_port = meta_1.egress_port;
          }
      }
      apply {
--- 20,31 ----
      }
  }
  control cIngress(inout headers_t hdr, inout metadata_t user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
      @name(".multicast") action multicast() {
          {
          }
          {
!             ostd.drop = false;
!             ostd.multicast_group = (MulticastGroup_t)hdr.ethernet.dstAddr[31:0];
          }
      }
      apply {
