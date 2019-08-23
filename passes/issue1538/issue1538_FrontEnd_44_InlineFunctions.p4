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
    bit<16> tmp_port_0;
    bit<16> tmp_1;
    bit<16> tmp_2;
    state start {
        {
            bit<16> x_1 = (bit<16>)standard_metadata.ingress_port;
            bool hasReturned = false;
            bit<16> retval;
            {
                hasReturned = true;
                retval = x_1 + 16w1;
            }
            tmp_1 = retval;
        }
        tmp_port_0 = tmp_1;
        packet.extract<ethernet_t>(hdr.ethernet);
        {
            bit<16> x_2 = hdr.ethernet.etherType;
            bool hasReturned = false;
            bit<16> retval;
            {
                hasReturned = true;
                retval = x_2 + 16w1;
            }
            tmp_2 = retval;
        }
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
        {
            bit<16> x_3 = hdr.ethernet.srcAddr[15:0];
            bool hasReturned_0 = false;
            bit<16> retval_0;
            bit<16> tmp;
            bit<16> tmp_0;
            {
                bit<16> x_0 = x_3;
                bool hasReturned = false;
                bit<16> retval;
                {
                    hasReturned = true;
                    retval = x_0 + 16w1;
                }
                tmp = retval;
            }
            tmp_0 = x_3 + tmp;
            {
                hasReturned_0 = true;
                retval_0 = tmp_0;
            }
            tmp_3 = retval_0;
        }
        hdr.ethernet.srcAddr[15:0] = tmp_3;
        {
            bit<16> x_4 = hdr.ethernet.srcAddr[15:0];
            bool hasReturned = false;
            bit<16> retval;
            {
                hasReturned = true;
                retval = x_4 + 16w1;
            }
            tmp_4 = retval;
        }
        hdr.ethernet.srcAddr[15:0] = tmp_4;
        {
            bit<16> x_5 = hdr.ethernet.etherType;
            bool hasReturned = false;
            bit<16> retval;
            {
                hasReturned = true;
                retval = x_5 + 16w1;
            }
            tmp_5 = retval;
        }
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
