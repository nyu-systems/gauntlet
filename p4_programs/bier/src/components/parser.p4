parser packetParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    // entry point
    state start {
        transition parse_ethernet;
    }

    // parse ethernet packet
    state parse_ethernet {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            TYPE_IPV4 :         parse_ipv4;
            TYPE_BIER :         parse_bier;
            TYPE_TOP_DISCOVER:  parse_topology_discover;
            default :           accept;
        }
    }

    // parse ipv4 packet
    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) {
            TYPE_IP_BIER: parse_bier;
            TYPE_IP_IGMP: parse_igmp;
            default: accept;
        }
    }

    // parse ipv4 inner
    state parse_ipv4_inner {
        packet.extract(hdr.ipv4_inner);
        transition accept;
    }


    // parse bier packet
    state parse_bier {
        packet.extract(hdr.bier);
        transition select(hdr.bier.Proto) {
            TYPE_IPV4: parse_ipv4_inner;
            default: accept;
        }
    }

    // parse topology disover
    state parse_topology_discover {
        packet.extract(hdr.topology);
        transition accept;
    }

    // parse igmp
    state parse_igmp {
        packet.extract(hdr.igmp);
        transition accept;
    }
}
