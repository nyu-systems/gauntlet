#include <core.p4>
#include <v1model.p4>
struct headers {
}
struct metadata {
}
parser ParserImpl(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}
bit<32> test_func() {
    return 32w1;
}
control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<32> value_0;
    @name("update_value") action update_value_0(out bit<32> value) {
        bit<32> tmp;
        {
            tmp = test_func();
            value = tmp;
        }
    }
    bit<32> tmp_0;
    apply {
        {
            tmp_0 = test_func();
            value_0 = tmp_0;
        }
        {
            update_value_0(value_0);
        }
    }
}
control VerifyChecksumImpl(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control EgressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}
control ComputeChecksumImpl(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
    }
}
V1Switch<headers, metadata>(ParserImpl(), VerifyChecksumImpl(), IngressImpl(), EgressImpl(), ComputeChecksumImpl(), DeparserImpl()) main;
