#include <core.p4>
#include <v1model.p4>
header hdr {
    bit<32> f;
}
struct Headers {
    hdr h;
}
struct Meta {
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
        {
            b.emit<hdr>(h.h);
        }
    }
}
control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    bit<32> v;
    @name("ingress.my_a") action my_a_0() {
        v = 32w0;
        h.h.f = v;
    }
    bit<32> v_1;
    @name("ingress.my_a") action my_a_2() {
        v_1 = 32w1;
        h.h.f = v_1;
    }
    apply {
        my_a_0();
        my_a_2();
    }
}
V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
