#include <core.p4>
#include <v1model.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Meta {
}

struct Headers {
    ethernet_t  eth_hdr;
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
    action set_mac(bit<48> dst_mac) {
        hdr.eth_hdr.dst_addr = dst_mac;
    }
    table simple_tbl {
        key = {
             hdr.eth_hdr.src_addr: exact;
        }
        actions = {
            NoAction;
            set_mac;
        }
    }
    apply {
        reset.apply(hdr.eth_hdr.src_addr);
        simple_tbl.apply();

    }
}


control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {b.emit(h);} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
