#include <core.p4>
#include <v1model.p4>


header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

struct Headers {
    ethernet_t eth_hdr;
}

struct Meta {
}

parser p(packet_in pkt, out Headers hdr, inout Meta meta, inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    action simple_action() {
        h.eth_hdr.eth_type = 16w3;
    }

    action dummy_action(inout bit<16> val1, in bit<16> val2) {}
    table simple_table {
        key = {
            h.eth_hdr.src_addr               : exact @name("key1") ;
        }
        actions = {
            simple_action();
        }
        default_action = simple_action();
    }
    apply {
        dummy_action(h.eth_hdr.eth_type, simple_table.apply().hit ? 16w1 : 16w2);
    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {
      b.emit(h);
    } }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
