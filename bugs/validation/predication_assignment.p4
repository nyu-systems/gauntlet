#include <core.p4>
#include <v1model.p4>

typedef bit<48>  EthernetAddress;

header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

header H {
    bit<4>  a;
    bit<4>  b;
}

struct Headers {
    Ethernet_h    ethernet;
    H    h;
}

struct Metadata {}


parser p(packet_in pkt,
               out Headers hdr, inout Metadata meta,
               inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract(hdr.ethernet);
        pkt.extract(hdr.h);
        transition accept;
    }
}

control ingress(inout Headers hdr, inout Metadata meta,
                 inout standard_metadata_t stdmeta) {
    action foo() {
        hdr.h.b = hdr.h.b + 5;
        if (hdr.h.b > 10) {
            hdr.h.b = hdr.h.b ^ 5;
            return;
        }
        hdr.h.b = hdr.h.b + 5;
    }

    apply {
        foo();
    }
}


control deparser(packet_out packet, in Headers hdr) {
    apply {
        packet.emit(hdr);
    }
}

control egress(inout Headers hdr, inout Metadata meta, inout standard_metadata_t stdmeta) {
    apply {}
}

control vrfy(inout Headers hdr, inout Metadata meta) {
    apply {}
}

control update(inout Headers hdr, inout Metadata meta) {
    apply {}
}

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

