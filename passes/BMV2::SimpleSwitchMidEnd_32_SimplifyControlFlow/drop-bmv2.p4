--- before_pass
+++ after_pass
@@ -12,55 +12,51 @@ parser ParserI(packet_in pk, out H hdr,
 control IngressI(inout H hdr, inout M meta, inout standard_metadata_t smeta) {
     standard_metadata_t smeta_1;
     @name(".drop") action drop_0() {
-        {
-            smeta_1.ingress_port = smeta.ingress_port;
-            smeta_1.egress_spec = smeta.egress_spec;
-            smeta_1.egress_port = smeta.egress_port;
-            smeta_1.clone_spec = smeta.clone_spec;
-            smeta_1.instance_type = smeta.instance_type;
-            smeta_1.drop = smeta.drop;
-            smeta_1.recirculate_port = smeta.recirculate_port;
-            smeta_1.packet_length = smeta.packet_length;
-            smeta_1.enq_timestamp = smeta.enq_timestamp;
-            smeta_1.enq_qdepth = smeta.enq_qdepth;
-            smeta_1.deq_timedelta = smeta.deq_timedelta;
-            smeta_1.deq_qdepth = smeta.deq_qdepth;
-            smeta_1.ingress_global_timestamp = smeta.ingress_global_timestamp;
-            smeta_1.egress_global_timestamp = smeta.egress_global_timestamp;
-            smeta_1.lf_field_list = smeta.lf_field_list;
-            smeta_1.mcast_grp = smeta.mcast_grp;
-            smeta_1.resubmit_flag = smeta.resubmit_flag;
-            smeta_1.egress_rid = smeta.egress_rid;
-            smeta_1.recirculate_flag = smeta.recirculate_flag;
-            smeta_1.checksum_error = smeta.checksum_error;
-            smeta_1.parser_error = smeta.parser_error;
-            smeta_1.priority = smeta.priority;
-        }
+        smeta_1.ingress_port = smeta.ingress_port;
+        smeta_1.egress_spec = smeta.egress_spec;
+        smeta_1.egress_port = smeta.egress_port;
+        smeta_1.clone_spec = smeta.clone_spec;
+        smeta_1.instance_type = smeta.instance_type;
+        smeta_1.drop = smeta.drop;
+        smeta_1.recirculate_port = smeta.recirculate_port;
+        smeta_1.packet_length = smeta.packet_length;
+        smeta_1.enq_timestamp = smeta.enq_timestamp;
+        smeta_1.enq_qdepth = smeta.enq_qdepth;
+        smeta_1.deq_timedelta = smeta.deq_timedelta;
+        smeta_1.deq_qdepth = smeta.deq_qdepth;
+        smeta_1.ingress_global_timestamp = smeta.ingress_global_timestamp;
+        smeta_1.egress_global_timestamp = smeta.egress_global_timestamp;
+        smeta_1.lf_field_list = smeta.lf_field_list;
+        smeta_1.mcast_grp = smeta.mcast_grp;
+        smeta_1.resubmit_flag = smeta.resubmit_flag;
+        smeta_1.egress_rid = smeta.egress_rid;
+        smeta_1.recirculate_flag = smeta.recirculate_flag;
+        smeta_1.checksum_error = smeta.checksum_error;
+        smeta_1.parser_error = smeta.parser_error;
+        smeta_1.priority = smeta.priority;
         mark_to_drop(smeta_1);
-        {
-            smeta.ingress_port = smeta_1.ingress_port;
-            smeta.egress_spec = smeta_1.egress_spec;
-            smeta.egress_port = smeta_1.egress_port;
-            smeta.clone_spec = smeta_1.clone_spec;
-            smeta.instance_type = smeta_1.instance_type;
-            smeta.drop = smeta_1.drop;
-            smeta.recirculate_port = smeta_1.recirculate_port;
-            smeta.packet_length = smeta_1.packet_length;
-            smeta.enq_timestamp = smeta_1.enq_timestamp;
-            smeta.enq_qdepth = smeta_1.enq_qdepth;
-            smeta.deq_timedelta = smeta_1.deq_timedelta;
-            smeta.deq_qdepth = smeta_1.deq_qdepth;
-            smeta.ingress_global_timestamp = smeta_1.ingress_global_timestamp;
-            smeta.egress_global_timestamp = smeta_1.egress_global_timestamp;
-            smeta.lf_field_list = smeta_1.lf_field_list;
-            smeta.mcast_grp = smeta_1.mcast_grp;
-            smeta.resubmit_flag = smeta_1.resubmit_flag;
-            smeta.egress_rid = smeta_1.egress_rid;
-            smeta.recirculate_flag = smeta_1.recirculate_flag;
-            smeta.checksum_error = smeta_1.checksum_error;
-            smeta.parser_error = smeta_1.parser_error;
-            smeta.priority = smeta_1.priority;
-        }
+        smeta.ingress_port = smeta_1.ingress_port;
+        smeta.egress_spec = smeta_1.egress_spec;
+        smeta.egress_port = smeta_1.egress_port;
+        smeta.clone_spec = smeta_1.clone_spec;
+        smeta.instance_type = smeta_1.instance_type;
+        smeta.drop = smeta_1.drop;
+        smeta.recirculate_port = smeta_1.recirculate_port;
+        smeta.packet_length = smeta_1.packet_length;
+        smeta.enq_timestamp = smeta_1.enq_timestamp;
+        smeta.enq_qdepth = smeta_1.enq_qdepth;
+        smeta.deq_timedelta = smeta_1.deq_timedelta;
+        smeta.deq_qdepth = smeta_1.deq_qdepth;
+        smeta.ingress_global_timestamp = smeta_1.ingress_global_timestamp;
+        smeta.egress_global_timestamp = smeta_1.egress_global_timestamp;
+        smeta.lf_field_list = smeta_1.lf_field_list;
+        smeta.mcast_grp = smeta_1.mcast_grp;
+        smeta.resubmit_flag = smeta_1.resubmit_flag;
+        smeta.egress_rid = smeta_1.egress_rid;
+        smeta.recirculate_flag = smeta_1.recirculate_flag;
+        smeta.checksum_error = smeta_1.checksum_error;
+        smeta.parser_error = smeta_1.parser_error;
+        smeta.priority = smeta_1.priority;
     }
     @name("IngressI.forward") table forward_0 {
         key = {
