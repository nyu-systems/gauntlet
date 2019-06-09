--- before_pass
+++ after_pass
@@ -205,7 +205,10 @@ parser ParserImpl(packet_in packet, out
     state Tcp_option_parser_parse_tcp_option_sack {
         {
             tmp = packet.lookahead<bit<16>>();
-            Tcp_option_parser_tmp_0 = {tmp[15:8],tmp[7:0]};
+            {
+                Tcp_option_parser_tmp_0.kind = tmp[15:8];
+                Tcp_option_parser_tmp_0.length = tmp[7:0];
+            }
         }
         Tcp_option_parser_n_sack_bytes = Tcp_option_parser_tmp_0.length;
         verify(Tcp_option_parser_n_sack_bytes == 8w10 || Tcp_option_parser_n_sack_bytes == 8w18 || Tcp_option_parser_n_sack_bytes == 8w26 || Tcp_option_parser_n_sack_bytes == 8w34, error.TcpBadSackOptionLength);
@@ -221,15 +224,107 @@ parser ParserImpl(packet_in packet, out
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
     @name("ingress.set_l2ptr") action set_l2ptr(bit<32> l2ptr) {
         meta.fwd_metadata.l2ptr = l2ptr;
@@ -268,9 +363,55 @@ control ingress(inout headers hdr, inout
 control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
     standard_metadata_t smeta_2;
     @name(".my_drop") action my_drop_1() {
-        smeta_2 = standard_metadata;
+        {
+            smeta_2.ingress_port = standard_metadata.ingress_port;
+            smeta_2.egress_spec = standard_metadata.egress_spec;
+            smeta_2.egress_port = standard_metadata.egress_port;
+            smeta_2.clone_spec = standard_metadata.clone_spec;
+            smeta_2.instance_type = standard_metadata.instance_type;
+            smeta_2.drop = standard_metadata.drop;
+            smeta_2.recirculate_port = standard_metadata.recirculate_port;
+            smeta_2.packet_length = standard_metadata.packet_length;
+            smeta_2.enq_timestamp = standard_metadata.enq_timestamp;
+            smeta_2.enq_qdepth = standard_metadata.enq_qdepth;
+            smeta_2.deq_timedelta = standard_metadata.deq_timedelta;
+            smeta_2.deq_qdepth = standard_metadata.deq_qdepth;
+            smeta_2.ingress_global_timestamp = standard_metadata.ingress_global_timestamp;
+            smeta_2.egress_global_timestamp = standard_metadata.egress_global_timestamp;
+            smeta_2.lf_field_list = standard_metadata.lf_field_list;
+            smeta_2.mcast_grp = standard_metadata.mcast_grp;
+            smeta_2.resubmit_flag = standard_metadata.resubmit_flag;
+            smeta_2.egress_rid = standard_metadata.egress_rid;
+            smeta_2.recirculate_flag = standard_metadata.recirculate_flag;
+            smeta_2.checksum_error = standard_metadata.checksum_error;
+            smeta_2.parser_error = standard_metadata.parser_error;
+            smeta_2.priority = standard_metadata.priority;
+        }
         mark_to_drop(smeta_2);
-        standard_metadata = smeta_2;
+        {
+            standard_metadata.ingress_port = smeta_2.ingress_port;
+            standard_metadata.egress_spec = smeta_2.egress_spec;
+            standard_metadata.egress_port = smeta_2.egress_port;
+            standard_metadata.clone_spec = smeta_2.clone_spec;
+            standard_metadata.instance_type = smeta_2.instance_type;
+            standard_metadata.drop = smeta_2.drop;
+            standard_metadata.recirculate_port = smeta_2.recirculate_port;
+            standard_metadata.packet_length = smeta_2.packet_length;
+            standard_metadata.enq_timestamp = smeta_2.enq_timestamp;
+            standard_metadata.enq_qdepth = smeta_2.enq_qdepth;
+            standard_metadata.deq_timedelta = smeta_2.deq_timedelta;
+            standard_metadata.deq_qdepth = smeta_2.deq_qdepth;
+            standard_metadata.ingress_global_timestamp = smeta_2.ingress_global_timestamp;
+            standard_metadata.egress_global_timestamp = smeta_2.egress_global_timestamp;
+            standard_metadata.lf_field_list = smeta_2.lf_field_list;
+            standard_metadata.mcast_grp = smeta_2.mcast_grp;
+            standard_metadata.resubmit_flag = smeta_2.resubmit_flag;
+            standard_metadata.egress_rid = smeta_2.egress_rid;
+            standard_metadata.recirculate_flag = smeta_2.recirculate_flag;
+            standard_metadata.checksum_error = smeta_2.checksum_error;
+            standard_metadata.parser_error = smeta_2.parser_error;
+            standard_metadata.priority = smeta_2.priority;
+        }
     }
     @name("egress.rewrite_mac") action rewrite_mac(bit<48> smac) {
         hdr.ethernet.srcAddr = smac;
