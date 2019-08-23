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
action my_drop(inout standard_metadata_t smeta_0) {
    mark_to_drop(smeta_0);
}
parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<16> tmp_port_1;
    bit<16> tmp_6;
    bit<16> tmp_7;
    state start {
        {
            bit<16> x = (bit<16>)standard_metadata.ingress_port;
            bool hasReturned_1 = false;
            bit<16> retval_1;
            hasReturned_1 = true;
            retval_1 = x + 16w1;
            tmp_6 = retval_1;
        }
        tmp_port_1 = tmp_6;
        packet.extract<ethernet_t>(hdr.ethernet);
        {
            bit<16> x_6 = hdr.ethernet.etherType;
            bool hasReturned_1 = false;
            bit<16> retval_1;
            hasReturned_1 = true;
            retval_1 = x_6 + 16w1;
            tmp_7 = retval_1;
        }
        hdr.ethernet.etherType = tmp_7;
        meta.tmp_port = tmp_port_1;
        transition accept;
    }
}
control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<16> tmp_8;
    bit<16> tmp_9;
    bit<16> tmp_10;
    @name("set_port") action set_port(bit<9> output_port) {
        standard_metadata.egress_spec = output_port;
    }
    @name("mac_da") table mac_da {
        key = {
            hdr.ethernet.dstAddr: exact @name("hdr.ethernet.dstAddr") ;
        }
        actions = {
            set_port();
            my_drop(standard_metadata);
        }
        default_action = my_drop(standard_metadata);
    }
    apply {
        mac_da.apply();
        {
            bit<16> x_7 = hdr.ethernet.srcAddr[15:0];
            bool hasReturned_2 = false;
            bit<16> retval_2;
            bit<16> tmp_11;
            bit<16> tmp_12;
            {
                bit<16> x_8 = x_7;
                bool hasReturned_1 = false;
                bit<16> retval_1;
                hasReturned_1 = true;
                retval_1 = x_8 + 16w1;
                tmp_11 = retval_1;
            }
            tmp_12 = x_7 + tmp_11;
            hasReturned_2 = true;
            retval_2 = tmp_12;
            tmp_8 = retval_2;
        }
        hdr.ethernet.srcAddr[15:0] = tmp_8;
        {
            bit<16> x_9 = hdr.ethernet.srcAddr[15:0];
            bool hasReturned_1 = false;
            bit<16> retval_1;
            hasReturned_1 = true;
            retval_1 = x_9 + 16w1;
            tmp_9 = retval_1;
        }
        hdr.ethernet.srcAddr[15:0] = tmp_9;
        {
            bit<16> x_10 = hdr.ethernet.etherType;
            bool hasReturned_1 = false;
            bit<16> retval_1;
            hasReturned_1 = true;
            retval_1 = x_10 + 16w1;
            tmp_10 = retval_1;
        }
        hdr.ethernet.etherType = tmp_10;
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
