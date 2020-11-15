#include <core.p4>
#define V1MODEL_VERSION 20180101
#include <v1model.p4>

struct ingress_metadata_t {
}

header H {
    bit<4> a;
}

struct metadata {
}

struct headers {
    H h;
}

parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract<H>(hdr = hdr.h);
        transition select(hdr.h.a) {
            4w4 &&& 4w0: reject;
            4w1 &&& 4w0: accept;
            4w2 &&& 4w0: accept;
            default: reject;
        }
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control ingress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
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

V1Switch<headers, metadata>(p = ParserImpl(), ig = ingress(), vr = verifyChecksum(), eg = egress(), ck = computeChecksum(), dep = DeparserImpl()) main;

