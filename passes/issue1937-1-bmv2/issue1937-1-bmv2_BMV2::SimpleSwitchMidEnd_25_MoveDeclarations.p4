#include <core.p4>
#include <v1model.p4>
header h1_t {
    bit<8> f1;
    bit<8> f2;
}
struct headers_t {
    h1_t h1;
}
struct metadata_t {
}
control ingressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    bit<8> tmp;
    bit<8> tmp_0;
    bit<8> x;
    bit<8> y;
    bit<8> x_1;
    bit<8> y_1;
    @name(".foo") action foo() {
        y = tmp_0;
        x = y >> 2;
        tmp = x;
    }
    @name(".foo") action foo_0() {
        y_1 = 8w5;
        x_1 = y_1 >> 2;
        hdr.h1.f2 = x_1;
    }
    apply {
        tmp_0 = hdr.h1.f1;
        foo();
        hdr.h1.f1 = tmp;
        foo_0();
    }
}
parser parserImpl(packet_in packet, out headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    state start {
        transition accept;
    }
}
control verifyChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply {
    }
}
control egressImpl(inout headers_t hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}
control updateChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply {
    }
}
control deparserImpl(packet_out packet, in headers_t hdr) {
    apply {
    }
}
V1Switch<headers_t, metadata_t>(parserImpl(), verifyChecksum(), ingressImpl(), egressImpl(), updateChecksum(), deparserImpl()) main;
