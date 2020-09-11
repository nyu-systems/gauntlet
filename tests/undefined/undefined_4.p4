#include <core.p4>
#include <v1model.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}


struct Headers {
    ethernet_t  eth_hdr;
}

struct Meta {
}

parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control reset_ctrl(out bit<48> reset) { apply {} }

control ingress(inout Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    reset_ctrl() reset;
    apply {
        reset.apply(hdr.eth_hdr.src_addr);
        if (hdr.eth_hdr.src_addr == 1) {
            hdr.eth_hdr.eth_type = 1;
        }
        if (hdr.eth_hdr.eth_type == 1) {
            hdr.eth_hdr.dst_addr = 1;
        }

    }
}


control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {b.emit(h);} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
