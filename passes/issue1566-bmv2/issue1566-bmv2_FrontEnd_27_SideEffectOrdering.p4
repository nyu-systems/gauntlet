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
control my_control_type(inout bit<16> x);
control C1(inout bit<16> x) {
    @name("stats") counter(32w65536, CounterType.packets) stats_0;
    apply {
        {
            x = x + 16w1;
        }
        {
            stats_0.count((bit<32>)x);
        }
    }
}
control C2(inout bit<16> x)(my_control_type c) {
    apply {
        {
            x = x << 1;
        }
        {
            c.apply(x);
        }
    }
}
control C3(inout bit<16> x)(my_control_type c) {
    apply {
        {
            x = x << 3;
        }
        {
            c.apply(x);
        }
    }
}
control E(inout bit<16> x) {
    @name("c1") C1() c1_0;
    @name("c2") C2(c1_0) c2_0;
    @name("c3") C3(c1_0) c3_0;
    apply {
        {
            c2_0.apply(x);
        }
        {
            c3_0.apply(x);
        }
    }
}
parser parserI(packet_in pkt, out Parsed_packet hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    state start {
        {
            pkt.extract<Ethernet_h>(hdr.ethernet);
        }
        transition accept;
    }
}
control cIngress(inout Parsed_packet hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    @name("E") E() E_inst_0;
    apply {
        {
            E_inst_0.apply(hdr.ethernet.etherType);
        }
    }
}
control cEgress(inout Parsed_packet hdr, inout metadata_t meta, inout standard_metadata_t stdmeta) {
    apply {
    }
}
control DeparserI(packet_out packet, in Parsed_packet hdr) {
    apply {
        {
            packet.emit<Ethernet_h>(hdr.ethernet);
        }
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
