#include <core.p4>
#include <v1model.p4>
extern jnf_counter {
    jnf_counter(CounterType type);
    void count();
}
struct metadata {
}
struct headers {
}
parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}
control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("c") jnf_counter(CounterType.packets) c_0;
    @name("a") action a_0() {
        {
            c_0.count();
        }
    }
    @name("t") table t_0 {
        actions = {
            a_0();
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        {
            t_0.apply();
        }
    }
}
control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}
control MyDeparser(packet_out packet, in headers hdr) {
    apply {
    }
}
control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
V1Switch<headers, metadata>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
