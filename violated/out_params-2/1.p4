#include <core.p4>
#include <v1model.p4>

header data_h {
    bit<32> f1;
    bit<32> f2;
    bit<16> h1;
    bit<8>  b1;
    bit<8>  b2;
}

header extra_h {
    bit<16> h;
    bit<8>  b1;
    bit<8>  b2;
}

struct packet_t {
    data_h     data;
    extra_h[4] extra;
}

struct Meta {
}

parser p(packet_in b, out packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
    state start {
        b.extract<data_h>(hdrs.data);
        transition extra;
    }
    state extra {
        b.extract<extra_h>(hdrs.extra.next);
        transition select(hdrs.extra.last.b2) {
            8w0x80 &&& 8w0x80: extra;
            default: accept;
        }
    }
}

control vrfy(inout packet_t h, inout Meta m) {
    apply {
    }
}

control update(inout packet_t h, inout Meta m) {
    apply {
    }
}

control ingress(inout packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
    @name("ingress.noop") action noop() {
    }
    bit<8> reg;
    @name("ingress.setbyte") action setbyte(bit<8> val) {
        reg = val;
        hdrs.data.b2 = reg + 1;
    }
    @name("ingress.tbl1") table tbl1_0 {
        key = {
            hdrs.data.f2: exact @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte();
            noop();
        }
        default_action = noop();
    }
    apply {
        tbl1_0.apply();
    }
}

control egress(inout packet_t hdrs, inout Meta m, inout standard_metadata_t meta) {
    apply {
    }
}

control deparser(packet_out b, in packet_t hdrs) {
    apply {
        b.emit<data_h>(hdrs.data);
        b.emit<extra_h[4]>(hdrs.extra);
    }
}

V1Switch<packet_t, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

