*** dumps/p4_16_samples/psa-multicast-basic-corrected-bmv2.p4/pruned/psa-multicast-basic-corrected-bmv2-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:14.976913900 +0200
--- dumps/p4_16_samples/psa-multicast-basic-corrected-bmv2.p4/pruned/psa-multicast-basic-corrected-bmv2-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:14.895498000 +0200
*************** control cIngress(inout headers_t hdr, in
*** 23,33 ****
      psa_ingress_output_metadata_t meta_1;
      MulticastGroup_t multicast_group_1;
      @name(".multicast") action multicast() {
!         meta_1 = ostd;
          multicast_group_1 = (MulticastGroup_t)hdr.ethernet.dstAddr[31:0];
          meta_1.drop = false;
          meta_1.multicast_group = multicast_group_1;
!         ostd = meta_1;
      }
      apply {
          multicast();
--- 23,49 ----
      psa_ingress_output_metadata_t meta_1;
      MulticastGroup_t multicast_group_1;
      @name(".multicast") action multicast() {
!         {
!             meta_1.class_of_service = ostd.class_of_service;
!             meta_1.clone = ostd.clone;
!             meta_1.clone_session_id = ostd.clone_session_id;
!             meta_1.drop = ostd.drop;
!             meta_1.resubmit = ostd.resubmit;
!             meta_1.multicast_group = ostd.multicast_group;
!             meta_1.egress_port = ostd.egress_port;
!         }
          multicast_group_1 = (MulticastGroup_t)hdr.ethernet.dstAddr[31:0];
          meta_1.drop = false;
          meta_1.multicast_group = multicast_group_1;
!         {
!             ostd.class_of_service = meta_1.class_of_service;
!             ostd.clone = meta_1.clone;
!             ostd.clone_session_id = meta_1.clone_session_id;
!             ostd.drop = meta_1.drop;
!             ostd.resubmit = meta_1.resubmit;
!             ostd.multicast_group = meta_1.multicast_group;
!             ostd.egress_port = meta_1.egress_port;
!         }
      }
      apply {
          multicast();
