#include <core.p4>
#define V1MODEL_VERSION 20180101
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
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    @name("simple_action") action simple_action_0() {
        h.eth_hdr.eth_type = 16w3;
    }
    @name("dummy_action") action dummy_action_0(inout bit<16> val1, in bit<16> val2) {
    }
    @name("simple_table") table simple_table_0 {
        key = {
            h.eth_hdr.src_addr: exact @name("key1") ;
        }
        actions = {
            simple_action_0();
        }
        default_action = simple_action_0();
    }
    apply {
        dummy_action_0(h.eth_hdr.eth_type, (simple_table_0.apply().hit ? 16w1 : 16w2));
    }
}

control vrfy(inout Headers h, inout Meta m) {
    apply {
    }
}

control update(inout Headers h, inout Meta m) {
    apply {
    }
}

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    apply {
    }
}

control deparser(packet_out b, in Headers h) {
    apply {
        b.emit<Headers>(h);
    }
}

V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

