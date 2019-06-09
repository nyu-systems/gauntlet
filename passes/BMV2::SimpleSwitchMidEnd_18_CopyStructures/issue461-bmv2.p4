--- before_pass
+++ after_pass
@@ -46,9 +46,55 @@ parser ParserImpl(packet_in packet, out
 control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     standard_metadata_t smeta;
     @name(".my_drop") action my_drop() {
-        smeta = standard_metadata;
+        {
+            smeta.ingress_port = standard_metadata.ingress_port;
+            smeta.egress_spec = standard_metadata.egress_spec;
+            smeta.egress_port = standard_metadata.egress_port;
+            smeta.clone_spec = standard_metadata.clone_spec;
+            smeta.instance_type = standard_metadata.instance_type;
+            smeta.drop = standard_metadata.drop;
+            smeta.recirculate_port = standard_metadata.recirculate_port;
+            smeta.packet_length = standard_metadata.packet_length;
+            smeta.enq_timestamp = standard_metadata.enq_timestamp;
+            smeta.enq_qdepth = standard_metadata.enq_qdepth;
+            smeta.deq_timedelta = standard_metadata.deq_timedelta;
+            smeta.deq_qdepth = standard_metadata.deq_qdepth;
+            smeta.ingress_global_timestamp = standard_metadata.ingress_global_timestamp;
+            smeta.egress_global_timestamp = standard_metadata.egress_global_timestamp;
+            smeta.lf_field_list = standard_metadata.lf_field_list;
+            smeta.mcast_grp = standard_metadata.mcast_grp;
+            smeta.resubmit_flag = standard_metadata.resubmit_flag;
+            smeta.egress_rid = standard_metadata.egress_rid;
+            smeta.recirculate_flag = standard_metadata.recirculate_flag;
+            smeta.checksum_error = standard_metadata.checksum_error;
+            smeta.parser_error = standard_metadata.parser_error;
+            smeta.priority = standard_metadata.priority;
+        }
         mark_to_drop(smeta);
-        standard_metadata = smeta;
+        {
+            standard_metadata.ingress_port = smeta.ingress_port;
+            standard_metadata.egress_spec = smeta.egress_spec;
+            standard_metadata.egress_port = smeta.egress_port;
+            standard_metadata.clone_spec = smeta.clone_spec;
+            standard_metadata.instance_type = smeta.instance_type;
+            standard_metadata.drop = smeta.drop;
+            standard_metadata.recirculate_port = smeta.recirculate_port;
+            standard_metadata.packet_length = smeta.packet_length;
+            standard_metadata.enq_timestamp = smeta.enq_timestamp;
+            standard_metadata.enq_qdepth = smeta.enq_qdepth;
+            standard_metadata.deq_timedelta = smeta.deq_timedelta;
+            standard_metadata.deq_qdepth = smeta.deq_qdepth;
+            standard_metadata.ingress_global_timestamp = smeta.ingress_global_timestamp;
+            standard_metadata.egress_global_timestamp = smeta.egress_global_timestamp;
+            standard_metadata.lf_field_list = smeta.lf_field_list;
+            standard_metadata.mcast_grp = smeta.mcast_grp;
+            standard_metadata.resubmit_flag = smeta.resubmit_flag;
+            standard_metadata.egress_rid = smeta.egress_rid;
+            standard_metadata.recirculate_flag = smeta.recirculate_flag;
+            standard_metadata.checksum_error = smeta.checksum_error;
+            standard_metadata.parser_error = smeta.parser_error;
+            standard_metadata.priority = smeta.priority;
+        }
     }
     @name("ingress.ipv4_da_lpm_stats") direct_counter(CounterType.packets) ipv4_da_lpm_stats_0;
     @name("ingress.set_l2ptr") action set_l2ptr(bit<32> l2ptr) {
@@ -94,9 +140,55 @@ control ingress(inout headers hdr, inout
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     standard_metadata_t smeta_1;
     @name(".my_drop") action my_drop_0() {
-        smeta_1 = standard_metadata;
+        {
+            smeta_1.ingress_port = standard_metadata.ingress_port;
+            smeta_1.egress_spec = standard_metadata.egress_spec;
+            smeta_1.egress_port = standard_metadata.egress_port;
+            smeta_1.clone_spec = standard_metadata.clone_spec;
+            smeta_1.instance_type = standard_metadata.instance_type;
+            smeta_1.drop = standard_metadata.drop;
+            smeta_1.recirculate_port = standard_metadata.recirculate_port;
+            smeta_1.packet_length = standard_metadata.packet_length;
+            smeta_1.enq_timestamp = standard_metadata.enq_timestamp;
+            smeta_1.enq_qdepth = standard_metadata.enq_qdepth;
+            smeta_1.deq_timedelta = standard_metadata.deq_timedelta;
+            smeta_1.deq_qdepth = standard_metadata.deq_qdepth;
+            smeta_1.ingress_global_timestamp = standard_metadata.ingress_global_timestamp;
+            smeta_1.egress_global_timestamp = standard_metadata.egress_global_timestamp;
+            smeta_1.lf_field_list = standard_metadata.lf_field_list;
+            smeta_1.mcast_grp = standard_metadata.mcast_grp;
+            smeta_1.resubmit_flag = standard_metadata.resubmit_flag;
+            smeta_1.egress_rid = standard_metadata.egress_rid;
+            smeta_1.recirculate_flag = standard_metadata.recirculate_flag;
+            smeta_1.checksum_error = standard_metadata.checksum_error;
+            smeta_1.parser_error = standard_metadata.parser_error;
+            smeta_1.priority = standard_metadata.priority;
+        }
         mark_to_drop(smeta_1);
-        standard_metadata = smeta_1;
+        {
+            standard_metadata.ingress_port = smeta_1.ingress_port;
+            standard_metadata.egress_spec = smeta_1.egress_spec;
+            standard_metadata.egress_port = smeta_1.egress_port;
+            standard_metadata.clone_spec = smeta_1.clone_spec;
+            standard_metadata.instance_type = smeta_1.instance_type;
+            standard_metadata.drop = smeta_1.drop;
+            standard_metadata.recirculate_port = smeta_1.recirculate_port;
+            standard_metadata.packet_length = smeta_1.packet_length;
+            standard_metadata.enq_timestamp = smeta_1.enq_timestamp;
+            standard_metadata.enq_qdepth = smeta_1.enq_qdepth;
+            standard_metadata.deq_timedelta = smeta_1.deq_timedelta;
+            standard_metadata.deq_qdepth = smeta_1.deq_qdepth;
+            standard_metadata.ingress_global_timestamp = smeta_1.ingress_global_timestamp;
+            standard_metadata.egress_global_timestamp = smeta_1.egress_global_timestamp;
+            standard_metadata.lf_field_list = smeta_1.lf_field_list;
+            standard_metadata.mcast_grp = smeta_1.mcast_grp;
+            standard_metadata.resubmit_flag = smeta_1.resubmit_flag;
+            standard_metadata.egress_rid = smeta_1.egress_rid;
+            standard_metadata.recirculate_flag = smeta_1.recirculate_flag;
+            standard_metadata.checksum_error = smeta_1.checksum_error;
+            standard_metadata.parser_error = smeta_1.parser_error;
+            standard_metadata.priority = smeta_1.priority;
+        }
     }
     @name("egress.rewrite_mac") action rewrite_mac(bit<48> smac) {
         hdr.ethernet.srcAddr = smac;
