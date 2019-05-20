*** dumps/p4_16_samples/std_meta_inlining.p4/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_17_SimplifyComparisons.p4	2019-05-20 17:00:32.417354200 +0200
--- dumps/p4_16_samples/std_meta_inlining.p4/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_18_CopyStructures.p4	2019-05-20 17:00:32.420734000 +0200
*************** control DeparserImpl(packet_out packet,
*** 16,24 ****
  control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
      standard_metadata_t standard_metadata_1;
      @name(".send_to_cpu") action send_to_cpu() {
!         standard_metadata_1 = standard_metadata;
          standard_metadata_1.egress_spec = 9w64;
!         standard_metadata = standard_metadata_1;
      }
      @name(".NoAction") action NoAction_0() {
      }
--- 16,68 ----
  control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
      standard_metadata_t standard_metadata_1;
      @name(".send_to_cpu") action send_to_cpu() {
!         {
!             standard_metadata_1.ingress_port = standard_metadata.ingress_port;
!             standard_metadata_1.egress_spec = standard_metadata.egress_spec;
!             standard_metadata_1.egress_port = standard_metadata.egress_port;
!             standard_metadata_1.clone_spec = standard_metadata.clone_spec;
!             standard_metadata_1.instance_type = standard_metadata.instance_type;
!             standard_metadata_1.drop = standard_metadata.drop;
!             standard_metadata_1.recirculate_port = standard_metadata.recirculate_port;
!             standard_metadata_1.packet_length = standard_metadata.packet_length;
!             standard_metadata_1.enq_timestamp = standard_metadata.enq_timestamp;
!             standard_metadata_1.enq_qdepth = standard_metadata.enq_qdepth;
!             standard_metadata_1.deq_timedelta = standard_metadata.deq_timedelta;
!             standard_metadata_1.deq_qdepth = standard_metadata.deq_qdepth;
!             standard_metadata_1.ingress_global_timestamp = standard_metadata.ingress_global_timestamp;
!             standard_metadata_1.egress_global_timestamp = standard_metadata.egress_global_timestamp;
!             standard_metadata_1.lf_field_list = standard_metadata.lf_field_list;
!             standard_metadata_1.mcast_grp = standard_metadata.mcast_grp;
!             standard_metadata_1.resubmit_flag = standard_metadata.resubmit_flag;
!             standard_metadata_1.egress_rid = standard_metadata.egress_rid;
!             standard_metadata_1.checksum_error = standard_metadata.checksum_error;
!             standard_metadata_1.recirculate_flag = standard_metadata.recirculate_flag;
!             standard_metadata_1.parser_error = standard_metadata.parser_error;
!         }
          standard_metadata_1.egress_spec = 9w64;
!         {
!             standard_metadata.ingress_port = standard_metadata_1.ingress_port;
!             standard_metadata.egress_spec = standard_metadata_1.egress_spec;
!             standard_metadata.egress_port = standard_metadata_1.egress_port;
!             standard_metadata.clone_spec = standard_metadata_1.clone_spec;
!             standard_metadata.instance_type = standard_metadata_1.instance_type;
!             standard_metadata.drop = standard_metadata_1.drop;
!             standard_metadata.recirculate_port = standard_metadata_1.recirculate_port;
!             standard_metadata.packet_length = standard_metadata_1.packet_length;
!             standard_metadata.enq_timestamp = standard_metadata_1.enq_timestamp;
!             standard_metadata.enq_qdepth = standard_metadata_1.enq_qdepth;
!             standard_metadata.deq_timedelta = standard_metadata_1.deq_timedelta;
!             standard_metadata.deq_qdepth = standard_metadata_1.deq_qdepth;
!             standard_metadata.ingress_global_timestamp = standard_metadata_1.ingress_global_timestamp;
!             standard_metadata.egress_global_timestamp = standard_metadata_1.egress_global_timestamp;
!             standard_metadata.lf_field_list = standard_metadata_1.lf_field_list;
!             standard_metadata.mcast_grp = standard_metadata_1.mcast_grp;
!             standard_metadata.resubmit_flag = standard_metadata_1.resubmit_flag;
!             standard_metadata.egress_rid = standard_metadata_1.egress_rid;
!             standard_metadata.checksum_error = standard_metadata_1.checksum_error;
!             standard_metadata.recirculate_flag = standard_metadata_1.recirculate_flag;
!             standard_metadata.parser_error = standard_metadata_1.parser_error;
!         }
      }
      @name(".NoAction") action NoAction_0() {
      }
