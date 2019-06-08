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
struct mystruct1 {
    bit<4> a;
    bit<4> b;
}
control DeparserI(packet_out packet, in Parsed_packet hdr) {
    apply {
        packet.emit<Ethernet_h>(hdr.ethernet);
    }
}
parser parserI(packet_in pkt, out Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract<Ethernet_h>(hdr.ethernet);
        transition accept;
    }
}
control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
    bool hasReturned_0;
    @name("cIngress.foo") action foo_0() {
        hasReturned_0 = false;
        meta.b = meta.b + 4w5;
        {
            bool cond;
            {
                bool pred;
                cond = meta.b > 4w10;
                pred = cond;
                {
                    meta.b = (pred ? meta.b ^ 4w5 : meta.b);
                    hasReturned_0 = (pred ? true : hasReturned_0);
                }
            }
        }
        {
            bool cond_0;
            {
                bool pred_0;
                cond_0 = !hasReturned_0;
                pred_0 = cond_0;
                meta.b = (pred_0 ? meta.b + 4w5 : meta.b);
            }
        }
    }
    @name("cIngress.guh") table guh {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
        }
        actions = {
            foo_0();
        }
        default_action = foo_0();
    }
    apply {
        guh.apply();
    }
}
control cEgress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}
control vc(inout Parsed_packet hdr, inout mystruct1 meta) {
    apply {
    }
}
control uc(inout Parsed_packet hdr, inout mystruct1 meta) {
    apply {
    }
}
V1Switch<Parsed_packet, mystruct1>(parserI(), vc(), cIngress(), cEgress(), uc(), DeparserI()) main;
