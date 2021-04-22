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

parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        pkt.extract<ethernet_t>(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    @name("ingress.tmp") bool tmp;
    @name("ingress.tmp_0") bool tmp_0;
    @name("ingress.hasReturned") bool hasReturned;
    @name("ingress.retval") bool retval;
    @name("eth_t") bit<16> eth_t;
    @name("target_addr") bit<48> target_addr;
    @name("check_bool") bool check_bool;
    @name(".assign") action assign() {
        eth_t = h.eth_hdr.eth_type;
        target_addr = h.eth_hdr.dst_addr;
        check_bool = true;
        {
            {
                {
                    bool cond;
                    cond = !tmp;
                    hasReturned = (check_bool ? true : hasReturned);
                    retval = (check_bool ? true : retval);
                    tmp = (check_bool ? retval : tmp);
                    tmp_0 = (check_bool ? (cond ? false : 16w0xdead != eth_t) : tmp_0);
                }
                {
                    target_addr = (check_bool ? (tmp_0 ? 48w1 : target_addr) : target_addr);
                }
            }
        }
        h.eth_hdr.eth_type = eth_t;
        h.eth_hdr.dst_addr = target_addr;
    }
    apply {
        assign();
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
        {
            b.emit<ethernet_t>(h.eth_hdr);
        }
    }
}

V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

