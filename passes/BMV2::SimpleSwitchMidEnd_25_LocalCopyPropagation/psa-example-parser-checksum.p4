*** dumps/p4_16_samples/psa-example-parser-checksum.p4/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-05-20 17:00:41.826064200 +0200
--- dumps/p4_16_samples/psa-example-parser-checksum.p4/pruned/psa-example-parser-checksum-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-05-20 17:00:41.835455700 +0200
*************** parser IngressParserImpl(packet_in buffe
*** 96,121 ****
      }
  }
  control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
-     psa_ingress_output_metadata_t meta_1;
      @name(".ingress_drop") action ingress_drop() {
          {
-             meta_1.class_of_service = ostd.class_of_service;
-             meta_1.clone = ostd.clone;
-             meta_1.clone_session_id = ostd.clone_session_id;
-             meta_1.drop = ostd.drop;
-             meta_1.resubmit = ostd.resubmit;
-             meta_1.multicast_group = ostd.multicast_group;
-             meta_1.egress_port = ostd.egress_port;
          }
-         meta_1.drop = true;
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
      @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(32w0) parser_error_counts;
--- 96,106 ----
      }
  }
  control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
      @name(".ingress_drop") action ingress_drop() {
          {
          }
          {
!             ostd.drop = true;
          }
      }
      @name("ingress.parser_error_counts") DirectCounter<PacketCounter_t>(32w0) parser_error_counts;
