#include <core.p4>
#include <v1model.p4>
bit<16> incr(in bit<16> x) {
    bool hasReturned = false;
    bit<16> retval;
    {
        hasReturned = true;
        retval = x + 16w1;
    }
    return retval;
}
bit<16> twoxplus1(in bit<16> x) {
    bool hasReturned_0 = false;
    bit<16> retval_0;
    bit<16> tmp;
    bit<16> tmp_0;
    tmp = incr(x);
    tmp_0 = x + tmp;
    {
        hasReturned_0 = true;
        retval_0 = tmp_0;
    }
    return retval_0;
}
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
    bit<16> tmp_port_0;
    bit<16> tmp_1;
    bit<16> tmp_2;
    state start {
        tmp_1 = incr((bit<16>)standard_metadata.ingress_port);
        tmp_port_0 = tmp_1;
        packet.extract<ethernet_t>(hdr.ethernet);
        tmp_2 = incr(hdr.ethernet.etherType);
        hdr.ethernet.etherType = tmp_2;
        meta.tmp_port = tmp_port_0;
        transition accept;
    }
}
control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<16> tmp_3;
    bit<16> tmp_4;
    bit<16> tmp_5;
    @name("set_port") action set_port_0(bit<9> output_port) {
        standard_metadata.egress_spec = output_port;
    }
    @name("mac_da") table mac_da_0 {
        key = {
            hdr.ethernet.dstAddr: exact @name("hdr.ethernet.dstAddr") ;
        }
        actions = {
            set_port_0();
            my_drop(standard_metadata);
        }
        default_action = my_drop(standard_metadata);
    }
    apply {
        mac_da_0.apply();
        tmp_3 = twoxplus1(hdr.ethernet.srcAddr[15:0]);
        hdr.ethernet.srcAddr[15:0] = tmp_3;
        tmp_4 = incr(hdr.ethernet.srcAddr[15:0]);
        hdr.ethernet.srcAddr[15:0] = tmp_4;
        tmp_5 = incr(hdr.ethernet.etherType);
        hdr.ethernet.etherType = tmp_5;
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
