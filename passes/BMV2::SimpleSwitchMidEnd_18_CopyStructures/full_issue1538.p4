#include <core.p4>
#include <v1model.p4>
struct metadata {
    bit<16> tmp_port;
}
header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}
struct headers {
    ethernet_t ethernet;
}
parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<16> tmp_port_0;
    bit<16> tmp;
    bit<16> tmp_0;
    bit<16> x_0;
    bool hasReturned;
    bit<16> retval;
    bit<16> x_1;
    bool hasReturned_0;
    bit<16> retval_0;
    state start {
        {
            x_0 = (bit<16>)standard_metadata.ingress_port;
            hasReturned = false;
            hasReturned = true;
            retval = x_0 + 16w1;
            tmp = retval;
        }
        tmp_port_0 = tmp;
        packet.extract<ethernet_t>(hdr.ethernet);
        {
            x_1 = hdr.ethernet.etherType;
            hasReturned_0 = false;
            hasReturned_0 = true;
            retval_0 = x_1 + 16w1;
            tmp_0 = retval_0;
        }
        hdr.ethernet.etherType = tmp_0;
        meta.tmp_port = tmp_port_0;
        transition accept;
    }
}
control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<16> tmp_1;
    bit<16> tmp_2;
    bit<16> tmp_3;
    bit<16> x_2;
    bool hasReturned_3;
    bit<16> retval_3;
    bit<16> tmp_4;
    bit<16> tmp_5;
    bit<16> x_3;
    bool hasReturned_4;
    bit<16> retval_4;
    bit<16> x_4;
    bool hasReturned_5;
    bit<16> retval_5;
    bit<16> x_5;
    bool hasReturned_6;
    bit<16> retval_6;
    standard_metadata_t smeta;
    @name(".my_drop") action my_drop() {
        {
            smeta.ingress_port = standard_metadata.ingress_port;
            smeta.egress_spec = standard_metadata.egress_spec;
            smeta.egress_port = standard_metadata.egress_port;
            smeta.clone_spec = standard_metadata.clone_spec;
            smeta.instance_type = standard_metadata.instance_type;
            smeta.drop = standard_metadata.drop;
            smeta.recirculate_port = standard_metadata.recirculate_port;
            smeta.packet_length = standard_metadata.packet_length;
            smeta.enq_timestamp = standard_metadata.enq_timestamp;
            smeta.enq_qdepth = standard_metadata.enq_qdepth;
            smeta.deq_timedelta = standard_metadata.deq_timedelta;
            smeta.deq_qdepth = standard_metadata.deq_qdepth;
            smeta.ingress_global_timestamp = standard_metadata.ingress_global_timestamp;
            smeta.egress_global_timestamp = standard_metadata.egress_global_timestamp;
            smeta.lf_field_list = standard_metadata.lf_field_list;
            smeta.mcast_grp = standard_metadata.mcast_grp;
            smeta.resubmit_flag = standard_metadata.resubmit_flag;
            smeta.egress_rid = standard_metadata.egress_rid;
            smeta.recirculate_flag = standard_metadata.recirculate_flag;
            smeta.checksum_error = standard_metadata.checksum_error;
            smeta.parser_error = standard_metadata.parser_error;
            smeta.priority = standard_metadata.priority;
        }
        mark_to_drop(smeta);
        {
            standard_metadata.ingress_port = smeta.ingress_port;
            standard_metadata.egress_spec = smeta.egress_spec;
            standard_metadata.egress_port = smeta.egress_port;
            standard_metadata.clone_spec = smeta.clone_spec;
            standard_metadata.instance_type = smeta.instance_type;
            standard_metadata.drop = smeta.drop;
            standard_metadata.recirculate_port = smeta.recirculate_port;
            standard_metadata.packet_length = smeta.packet_length;
            standard_metadata.enq_timestamp = smeta.enq_timestamp;
            standard_metadata.enq_qdepth = smeta.enq_qdepth;
            standard_metadata.deq_timedelta = smeta.deq_timedelta;
            standard_metadata.deq_qdepth = smeta.deq_qdepth;
            standard_metadata.ingress_global_timestamp = smeta.ingress_global_timestamp;
            standard_metadata.egress_global_timestamp = smeta.egress_global_timestamp;
            standard_metadata.lf_field_list = smeta.lf_field_list;
            standard_metadata.mcast_grp = smeta.mcast_grp;
            standard_metadata.resubmit_flag = smeta.resubmit_flag;
            standard_metadata.egress_rid = smeta.egress_rid;
            standard_metadata.recirculate_flag = smeta.recirculate_flag;
            standard_metadata.checksum_error = smeta.checksum_error;
            standard_metadata.parser_error = smeta.parser_error;
            standard_metadata.priority = smeta.priority;
        }
    }
    @name("ingress.set_port") action set_port(bit<9> output_port) {
        standard_metadata.egress_spec = output_port;
    }
    @name("ingress.mac_da") table mac_da_0 {
        key = {
            hdr.ethernet.dstAddr: exact @name("hdr.ethernet.dstAddr") ;
        }
        actions = {
            set_port();
            my_drop();
        }
        default_action = my_drop();
    }
    apply {
        mac_da_0.apply();
        {
            x_2 = hdr.ethernet.srcAddr[15:0];
            hasReturned_3 = false;
            {
                x_3 = x_2;
                hasReturned_4 = false;
                hasReturned_4 = true;
                retval_4 = x_3 + 16w1;
                tmp_4 = retval_4;
            }
            tmp_5 = x_2 + tmp_4;
            hasReturned_3 = true;
            retval_3 = tmp_5;
            tmp_1 = retval_3;
        }
        hdr.ethernet.srcAddr[15:0] = tmp_1;
        {
            x_4 = hdr.ethernet.srcAddr[15:0];
            hasReturned_5 = false;
            hasReturned_5 = true;
            retval_5 = x_4 + 16w1;
            tmp_2 = retval_5;
        }
        hdr.ethernet.srcAddr[15:0] = tmp_2;
        {
            x_5 = hdr.ethernet.etherType;
            hasReturned_6 = false;
            hasReturned_6 = true;
            retval_6 = x_5 + 16w1;
            tmp_3 = retval_6;
        }
        hdr.ethernet.etherType = tmp_3;
    }
}
control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}
control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
    }
}
control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
V1Switch<headers, metadata>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
