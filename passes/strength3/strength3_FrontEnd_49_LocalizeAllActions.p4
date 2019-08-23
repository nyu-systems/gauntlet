#include <core.p4>
#include <v1model.p4>
header hdr {
    bit<16> a;
    bit<16> b;
    bit<8>  c;
}
struct Headers {
    hdr h;
}
struct Meta {
    bit<8> x;
    bit<8> y;
}
control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    @name("case0") action case0_0() {
        h.h.c = (bit<8>)((16w0 ++ h.h.a)[15:0] ++ 16w0);
    }
    @name("case1") action case1_0() {
        h.h.c = (bit<8>)h.h.a[15:0];
    }
    @name("case2") action case2_0() {
        h.h.c = 8w0;
    }
    @name("case3") action case3_0() {
        h.h.c = h.h.a[7:0];
    }
    @name("case4") action case4_0() {
        h.h.c = (bit<8>)(8w0 ++ h.h.a[15:0]);
    }
    @name("case5") action case5_0() {
        h.h.c = (bit<8>)(8w0 ++ h.h.a[15:8]);
    }
    @name("case6") action case6_0() {
        h.h.c = (bit<8>)(16w0 ++ h.h.a[15:8]);
    }
    @name("case7") action case7_0() {
        h.h.c = (bit<8>)(16w0 ++ h.h.a >> 3)[31:8];
    }
    @name("t") table t {
        actions = {
            case0_0();
            case1_0();
            case2_0();
            case3_0();
            case4_0();
            case5_0();
            case6_0();
            case7_0();
        }
        const default_action = case0_0();
    }
    apply {
        t.apply();
    }
}
parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
    state start {
        b.extract<hdr>(h.h);
        transition accept;
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
        b.emit<hdr>(h.h);
    }
}
V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
