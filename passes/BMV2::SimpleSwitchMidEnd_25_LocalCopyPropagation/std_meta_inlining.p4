--- dumps/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:34:04.228155100 +0200
+++ dumps/pruned/std_meta_inlining-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:34:04.229792300 +0200
@@ -14,54 +14,11 @@ control DeparserImpl(packet_out packet,
     }
 }
 control ingress(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t standard_metadata) {
-    standard_metadata_t standard_metadata_1;
     @name(".send_to_cpu") action send_to_cpu() {
         {
-            standard_metadata_1.ingress_port = standard_metadata.ingress_port;
-            standard_metadata_1.egress_spec = standard_metadata.egress_spec;
-            standard_metadata_1.egress_port = standard_metadata.egress_port;
-            standard_metadata_1.clone_spec = standard_metadata.clone_spec;
-            standard_metadata_1.instance_type = standard_metadata.instance_type;
-            standard_metadata_1.drop = standard_metadata.drop;
-            standard_metadata_1.recirculate_port = standard_metadata.recirculate_port;
-            standard_metadata_1.packet_length = standard_metadata.packet_length;
-            standard_metadata_1.enq_timestamp = standard_metadata.enq_timestamp;
-            standard_metadata_1.enq_qdepth = standard_metadata.enq_qdepth;
-            standard_metadata_1.deq_timedelta = standard_metadata.deq_timedelta;
-            standard_metadata_1.deq_qdepth = standard_metadata.deq_qdepth;
-            standard_metadata_1.ingress_global_timestamp = standard_metadata.ingress_global_timestamp;
-            standard_metadata_1.egress_global_timestamp = standard_metadata.egress_global_timestamp;
-            standard_metadata_1.lf_field_list = standard_metadata.lf_field_list;
-            standard_metadata_1.mcast_grp = standard_metadata.mcast_grp;
-            standard_metadata_1.resubmit_flag = standard_metadata.resubmit_flag;
-            standard_metadata_1.egress_rid = standard_metadata.egress_rid;
-            standard_metadata_1.checksum_error = standard_metadata.checksum_error;
-            standard_metadata_1.recirculate_flag = standard_metadata.recirculate_flag;
-            standard_metadata_1.parser_error = standard_metadata.parser_error;
         }
-        standard_metadata_1.egress_spec = 9w64;
         {
-            standard_metadata.ingress_port = standard_metadata_1.ingress_port;
-            standard_metadata.egress_spec = standard_metadata_1.egress_spec;
-            standard_metadata.egress_port = standard_metadata_1.egress_port;
-            standard_metadata.clone_spec = standard_metadata_1.clone_spec;
-            standard_metadata.instance_type = standard_metadata_1.instance_type;
-            standard_metadata.drop = standard_metadata_1.drop;
-            standard_metadata.recirculate_port = standard_metadata_1.recirculate_port;
-            standard_metadata.packet_length = standard_metadata_1.packet_length;
-            standard_metadata.enq_timestamp = standard_metadata_1.enq_timestamp;
-            standard_metadata.enq_qdepth = standard_metadata_1.enq_qdepth;
-            standard_metadata.deq_timedelta = standard_metadata_1.deq_timedelta;
-            standard_metadata.deq_qdepth = standard_metadata_1.deq_qdepth;
-            standard_metadata.ingress_global_timestamp = standard_metadata_1.ingress_global_timestamp;
-            standard_metadata.egress_global_timestamp = standard_metadata_1.egress_global_timestamp;
-            standard_metadata.lf_field_list = standard_metadata_1.lf_field_list;
-            standard_metadata.mcast_grp = standard_metadata_1.mcast_grp;
-            standard_metadata.resubmit_flag = standard_metadata_1.resubmit_flag;
-            standard_metadata.egress_rid = standard_metadata_1.egress_rid;
-            standard_metadata.checksum_error = standard_metadata_1.checksum_error;
-            standard_metadata.recirculate_flag = standard_metadata_1.recirculate_flag;
-            standard_metadata.parser_error = standard_metadata_1.parser_error;
+            standard_metadata.egress_spec = 9w64;
         }
     }
     @name(".NoAction") action NoAction_0() {
