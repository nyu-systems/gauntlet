#include <core.p4>
#include <v1model.p4>

struct Headers {
    bit<64> a;
    bit<32> b;
    bit<32> c;
}

struct Metadata {
}

parser P(packet_in b, out Headers p, inout Metadata meta, inout standard_metadata_t standard_meta) {
    state start {
        transition accept;
    }
}

control Ing(inout Headers headers, inout Metadata meta, inout standard_metadata_t standard_meta) {
    bit<32> _sub_0;
    bit<64> res_0;
    bit<32> tmp;
    bool p_1;
    bit<64> val;
    @name("Eg.update") action update() {
        p_1 = true;
        val = res_0;
        _sub_0 = val[31:0];
        {
            bool cond;
            {
                bool pred;
                cond = p_1;
                pred = cond;
                tmp = (pred ? _sub_0 : tmp);
                cond = !cond;
                pred = cond;
                tmp = (pred ? tmp: 32w1);
            }
        }
        _sub_0 = tmp;
        val[31:0] = _sub_0;
        res_0 = val;
    }
    apply {
        res_0 = 64w0;
        update();
        headers.a = res_0;
    }
}

control Eg(inout Headers hdrs, inout Metadata meta, inout standard_metadata_t standard_meta) {
    apply {
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

