#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header H {
    bit<8> a;
}

header I {
    bit<16> etherType;
}

struct h {
    ethernet_t ether;
    H          h;
    I          i;
}

struct m {
}

parser L3(packet_in b, inout h hdr) {
    bit<16> etherType_0;
    state start {
        etherType_0 = hdr.ether.etherType;
        transition select(etherType_0) {
            16w0x800: h;
            16w0x8100: i;
            default: accept;
        }
    }
    state h {
        b.extract<H>(hdr.h);
        transition accept;
    }
    state i {
        b.extract<I>(hdr.i);
        etherType_0 = hdr.i.etherType;
        transition start;
    }
}

parser MyParser(packet_in b, out h hdr, inout m meta, inout standard_metadata_t std) {
    @name("l3") L3() l3_0;
    state start {
        b.extract<ethernet_t>(hdr.ether);
        l3_0.apply(b, hdr);
        transition accept;
    }
}

control MyVerifyChecksum(inout h hdr, inout m meta) {
    apply {
    }
}

control MyIngress(inout h hdr, inout m meta, inout standard_metadata_t std) {
    apply {
    }
}

control MyEgress(inout h hdr, inout m meta, inout standard_metadata_t std) {
    apply {
    }
}

control MyComputeChecksum(inout h hdr, inout m meta) {
    apply {
    }
}

control MyDeparser(packet_out b, in h hdr) {
    apply {
        b.emit<h>(hdr);
    }
}

V1Switch<h, m>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;

