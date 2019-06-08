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
    bool hasReturned_0;
    bit<32> retval_0;
    hasReturned_0 = false;
    hasReturned_0 = true;
    retval_0 = 32w1;
    return retval_0;
}
control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<32> value_2;
    bit<32> tmp_1;
    bit<32> tmp_2;
    bool hasReturned_1;
    bit<32> retval_1;
    bit<32> value_0;
    @name("IngressImpl.update_value") action update_value_0() {
        {
            hasReturned_1 = false;
            hasReturned_1 = true;
            retval_1 = 32w1;
            tmp_1 = retval_1;
        }
        value_0 = tmp_1;
        value_2 = value_0;
    }
    apply {
        tmp_2 = test_func();
        update_value_0();
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
