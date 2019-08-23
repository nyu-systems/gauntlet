#include <core.p4>
#include <v1model.p4>
typedef bit<48> EthernetAddress;
header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}
struct Parsed_packet {
    Ethernet_h ethernet;
}
struct metadata_t {
    bit<4> a;
    bit<4> b;
}
control DeparserI(packet_out packet, in Parsed_packet hdr) {
    apply {
        packet.emit<Ethernet_h>(hdr.ethernet);
    }
}
parser parserI(packet_in pkt, out Parsed_packet hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract<Ethernet_h>(hdr.ethernet);
        transition accept;
    }
}
control cIngress(inout Parsed_packet hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    @name("a1") action a1_0() {
        hdr.ethernet.srcAddr = 48w1;
    }
    @name("a2") action a2_0() {
        hdr.ethernet.srcAddr[47:40] = 8w2;
    }
    @name("a3") action a3_0() {
        hdr.ethernet.srcAddr[47:40] = 8w3;
    }
    @name("a4") action a4_0() {
        hdr.ethernet.srcAddr[47:40] = 8w4;
    }
    @name("t1") table t1_0 {
        key = {
            hdr.ethernet.dstAddr: exact @name("hdr.ethernet.dstAddr") ;
        }
        actions = {
            a1_0();
            a2_0();
            a3_0();
            a4_0();
            NoAction();
        }
        default_action = NoAction();
    }
    apply {
        switch (t1_0.apply().action_run) {
            a1_0: {
            }
            a2_0: {
                hdr.ethernet.srcAddr[39:32] = 8w2;
            }
            a3_0: {
                hdr.ethernet.srcAddr[39:32] = 8w3;
            }
            a4_0: {
                hdr.ethernet.srcAddr[39:32] = 8w4;
            }
            NoAction: {
                hdr.ethernet.srcAddr[39:32] = 8w5;
            }
        }
    }
}
control cEgress(inout Parsed_packet hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}
control vc(inout Parsed_packet hdr, inout metadata_t meta) {
    apply {
    }
}
control uc(inout Parsed_packet hdr, inout metadata_t meta) {
    apply {
    }
}
V1Switch<Parsed_packet, metadata_t>(parserI(), vc(), cIngress(), cEgress(), uc(), DeparserI()) main;
