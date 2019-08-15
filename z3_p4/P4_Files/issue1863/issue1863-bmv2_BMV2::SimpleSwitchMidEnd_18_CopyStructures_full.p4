#include <core.p4>
#include <v1model.p4>
typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}
header custom_t {
    bit<8> a;
    bit<8> b;
}
struct headers_t {
    ethernet_t ethernet;
    custom_t   custom;
}
struct foo_t {
    bit<8> a;
    bit<8> b;
}
struct metadata_t {
}
parser parserImpl(packet_in packet, out headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    state start {
        packet.extract<ethernet_t>(hdr.ethernet);
        packet.extract<custom_t>(hdr.custom);
        transition accept;
    }
}
control verifyChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply {
    }
}
control ingressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    foo_t foo_0;
    apply {
        stdmeta.egress_spec = 9w0;
        {
            foo_0.a = 8w1;
            foo_0.b = 8w2;
        }
        {
            foo_0.a = foo_0.b;
            foo_0.b = foo_0.a;
        }
        hdr.custom.a = foo_0.a;
        hdr.custom.b = foo_0.b;
    }
}
control egressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}
control updateChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply {
    }
}
control deparserImpl(packet_out packet, in headers_t hdr) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<custom_t>(hdr.custom);
    }
}
V1Switch<headers_t, metadata_t>(parserImpl(), verifyChecksum(), ingressImpl(), egressImpl(), updateChecksum(), deparserImpl()) main;
