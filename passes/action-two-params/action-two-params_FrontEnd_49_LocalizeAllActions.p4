#include <core.p4>
#include <v1model.p4>
typedef bit<48> mac_addr_t;
typedef bit<32> IPv4Address;
header ethernet_t {
    mac_addr_t dstAddr;
    mac_addr_t srcAddr;
    bit<16>    etherType;
}
header ipv4_t {
    bit<4>      version;
    bit<4>      ihl;
    bit<8>      diffserv;
    bit<16>     packet_length;
    bit<16>     identification;
    bit<3>      flags;
    bit<13>     fragOffset;
    bit<8>      ttl;
    bit<8>      protocol;
    bit<16>     hdrChecksum;
    IPv4Address srcAddr;
    IPv4Address dstAddr;
}
struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
}
struct metadata {
}
parser MyParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}
control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    @name("drop") action drop_0() {
        mark_to_drop(standard_metadata);
    }
    @name("actTbl") action actTbl_0(bit<24> id, bit<32> ip) {
    }
    @name("ingress_tbl") table ingress_tbl {
        key = {
            hdr.ipv4.dstAddr: exact @name("hdr.ipv4.dstAddr") ;
        }
        actions = {
            actTbl_0();
            drop_0();
        }
        const default_action = drop_0();
        const entries = {
                        32w0x20020420 : actTbl_0(24w42, 32w0x20024200);
        }
    }
    apply {
        if (hdr.ipv4.isValid()) {
            ingress_tbl.apply();
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
control MyVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
V1Switch<headers, metadata>(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
