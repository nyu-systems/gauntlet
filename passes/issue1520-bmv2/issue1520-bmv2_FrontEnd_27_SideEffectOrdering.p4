#include <core.p4>
#include <v1model.p4>
header Header {
    bit<16> x;
}
struct headers {
    Header h;
}
struct metadata {
}
parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state start {
        {
            hdr.h.x = 16w0;
        }
        transition accept;
    }
}
control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control C(inout headers hdr, inout metadata meta)(bool b) {
    @name("r") register<bit<16>>(32w8) r_0;
    apply {
        {
            r_0.read(hdr.h.x, 32w0);
        }
    }
}
control H(inout headers hdr, inout metadata meta) {
    @name("c1") C(true) c1_0;
    @name("c2") C(false) c2_0;
    apply {
        {
            c1_0.apply(hdr, meta);
        }
        {
            c2_0.apply(hdr, meta);
        }
    }
}
control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("h") H() h_0;
    apply {
        {
            h_0.apply(hdr, meta);
        }
    }
}
control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}
control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control MyDeparser(packet_out packet, in headers hdr) {
    apply {
    }
}
V1Switch<headers, metadata>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
