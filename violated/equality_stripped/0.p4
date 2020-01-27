#include <core.p4>
#include <v1model.p4>

header H {
    bit<8>     s;
    varbit<32> v;
}

struct metadata {
}

struct headers {
    H    h;
    H    b;
}


parser p(packet_in b, out headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
    state start {
        b.extract<H>(hdr);
        transition accept;
    }
}

control ingress(inout headers hdr) {
    apply {
            hdr.h.s = hdr.h.s + 8w2;
    }
}

control egress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}

control vc(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control uc(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control deparser(packet_out packet, in headers hdr) {
    apply {
        {
            packet.emit<H>(hdr.h);
        }
    }
}

V1Switch<headers, metadata>(p(), vc(), ingress(), egress(), uc(), deparser()) main;

