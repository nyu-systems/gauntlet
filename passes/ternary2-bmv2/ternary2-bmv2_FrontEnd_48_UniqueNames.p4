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
    @name("setb1") action setb1(bit<9> port, bit<8> val) {
        hdrs.data.b1 = val;
        meta.egress_spec = port;
    }
    @name("noop") action noop() {
    }
    @name("setbyte") action setbyte(out bit<8> reg_0, bit<8> val) {
        reg_0 = val;
    }
    @name("act1") action act1(bit<8> val) {
        hdrs.extra[0].b1 = val;
    }
    @name("act2") action act2(bit<8> val) {
        hdrs.extra[0].b1 = val;
    }
    @name("act3") action act3(bit<8> val) {
        hdrs.extra[0].b1 = val;
    }
    @name("test1") table test1 {
        key = {
            hdrs.data.f1: ternary @name("hdrs.data.f1") ;
        }
        actions = {
            setb1();
            noop();
        }
        default_action = noop();
    }
    @name("ex1") table ex1 {
        key = {
            hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
        }
        actions = {
            setbyte(hdrs.extra[0].b1);
            act1();
            act2();
            act3();
            noop();
        }
        default_action = noop();
    }
    @name("tbl1") table tbl1 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte(hdrs.data.b2);
            noop();
        }
        default_action = noop();
    }
    @name("tbl2") table tbl2 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte(hdrs.extra[1].b1);
            noop();
        }
        default_action = noop();
    }
    @name("tbl3") table tbl3 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte(hdrs.extra[2].b2);
            noop();
        }
        default_action = noop();
    }
    apply {
        test1.apply();
        switch (ex1.apply().action_run) {
            act1: {
                tbl1.apply();
            }
            act2: {
                tbl2.apply();
            }
            act3: {
                tbl3.apply();
            }
        }
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
