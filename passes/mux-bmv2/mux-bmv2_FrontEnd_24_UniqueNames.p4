#include <core.p4>
#include <v1model.p4>
struct Headers {
}
struct Metadata {
}
parser P(packet_in b, out Headers p, inout Metadata meta, inout standard_metadata_t standard_meta) {
    state start {
        transition accept;
    }
}
control Ing(inout Headers headers, inout Metadata meta, inout standard_metadata_t standard_meta) {
    apply {
    }
}
control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
    @name("update") action update_0(in bool p, inout bit<64> val) {
        bit<32> _sub_0 = val[31:0];
        _sub_0 = (p ? _sub_0 : 32w1);
        val[31:0] = _sub_0;
    }
    apply {
        bit<64> res_0 = 64w0;
        update_0(true, res_0);
    }
}
control DP(packet_out b, in Headers p) {
    apply {
    }
}
control Verify(inout Headers hdrs, inout Metadata meta) {
    apply {
    }
}
control Compute(inout Headers hdr, inout Metadata meta) {
    apply {
    }
}
V1Switch<Headers, Metadata>(P(), Verify(), Ing(), Eg(), Compute(), DP()) main;
