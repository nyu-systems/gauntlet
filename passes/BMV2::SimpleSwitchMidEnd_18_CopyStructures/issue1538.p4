--- before_pass
+++ after_pass
@@ -63,9 +63,55 @@ control ingress(inout headers hdr, inout
     bit<16> retval_6;
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
     @name("ingress.set_port") action set_port(bit<9> output_port) {
         standard_metadata.egress_spec = output_port;
