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
    @name("noop") action noop_5() {
    }
    @name("noop") action noop_6() {
    }
    @name("noop") action noop_7() {
    }
    @name("noop") action noop_8() {
    }
    @name("setbyte") action setbyte(out bit<8> reg, bit<8> val) {
        reg = val;
    }
    @name("setbyte") action setbyte_4(out bit<8> reg_1, bit<8> val) {
        reg_1 = val;
    }
    @name("setbyte") action setbyte_5(out bit<8> reg_2, bit<8> val) {
        reg_2 = val;
    }
    @name("setbyte") action setbyte_6(out bit<8> reg_3, bit<8> val) {
        reg_3 = val;
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
    @name("test1") table test1_0 {
        key = {
            hdrs.data.f1: ternary @name("hdrs.data.f1") ;
        }
        actions = {
            setb1();
            noop();
        }
        default_action = noop();
    }
    @name("ex1") table ex1_0 {
        key = {
            hdrs.extra[0].h: ternary @name("hdrs.extra[0].h") ;
        }
        actions = {
            setbyte(hdrs.extra[0].b1);
            act1();
            act2();
            act3();
            noop_5();
        }
        default_action = noop_5();
    }
    @name("tbl1") table tbl1_0 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte_4(hdrs.data.b2);
            noop_6();
        }
        default_action = noop_6();
    }
    @name("tbl2") table tbl2_0 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte_5(hdrs.extra[1].b1);
            noop_7();
        }
        default_action = noop_7();
    }
    @name("tbl3") table tbl3_0 {
        key = {
            hdrs.data.f2: ternary @name("hdrs.data.f2") ;
        }
        actions = {
            setbyte_6(hdrs.extra[2].b2);
            noop_8();
        }
        default_action = noop_8();
    }
    apply {
        test1_0.apply();
        switch (ex1_0.apply().action_run) {
            act1: {
                tbl1_0.apply();
            }
            act2: {
                tbl2_0.apply();
            }
            act3: {
                tbl3_0.apply();
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
