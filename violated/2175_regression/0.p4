#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header H {
    bit<8> a;
    bit<8> b;
}

struct Parsed_packet {
    ethernet_t eth;
    H          h;
}

struct Metadata {
}

control deparser(packet_out packet, in Parsed_packet hdr) {
    apply {
        packet.emit<Parsed_packet>(hdr);
    }
}

parser p(packet_in pkt, out Parsed_packet hdr, inout Metadata meta, inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract<ethernet_t>(hdr.eth);
        pkt.extract<H>(hdr.h);
        transition accept;
    }
}

void do_something(inout bit<8> val) {
    if (val == 8w0) {
        ;
        return;
    }
    val = 8w2;
    return;
}
control ingress(inout Parsed_packet h, inout Metadata m, inout standard_metadata_t sm) {
    apply {
        do_something(h.h.b);
    }
}

control egress(inout Parsed_packet hdr, inout Metadata meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}

control vrfy(inout Parsed_packet hdr, inout Metadata meta) {
    apply {
    }
}

control update(inout Parsed_packet hdr, inout Metadata meta) {
    apply {
    }
}

V1Switch<Parsed_packet, Metadata>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

