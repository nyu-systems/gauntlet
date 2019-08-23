#include <core.p4>
#include <psa.p4>
typedef bit<48> EthernetAddress;
header ethernet_t {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}
header ipv4_t {
    bit<4>  version;
    bit<4>  ihl;
    bit<8>  diffserv;
    bit<16> totalLen;
    bit<16> identification;
    bit<3>  flags;
    bit<13> fragOffset;
    bit<8>  ttl;
    bit<8>  protocol;
    bit<16> hdrChecksum;
    bit<32> srcAddr;
    bit<32> dstAddr;
}
struct empty_metadata_t {
}
struct fwd_metadata_t {
}
struct metadata {
    fwd_metadata_t fwd_metadata;
}
typedef bit<48> ByteCounter_t;
typedef bit<80> PacketByteCounter_t;
struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
}
parser CommonParser(packet_in buffer, out headers parsed_hdr, inout metadata user_meta) {
    state start {
        {
            buffer.extract<ethernet_t>(parsed_hdr.ethernet);
        }
        transition select(parsed_hdr.ethernet.etherType) {
            16w0x800: parse_ipv4;
            default: accept;
        }
    }
    state parse_ipv4 {
        {
            buffer.extract<ipv4_t>(parsed_hdr.ipv4);
        }
        transition accept;
    }
}
parser IngressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_ingress_parser_input_metadata_t istd, in empty_metadata_t resubmit_meta, in empty_metadata_t recirculate_meta) {
    @name("p") CommonParser() p_0;
    state start {
        {
            p_0.apply(buffer, parsed_hdr, user_meta);
        }
        transition accept;
    }
}
parser EgressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata user_meta, in psa_egress_parser_input_metadata_t istd, in empty_metadata_t normal_meta, in empty_metadata_t clone_i2e_meta, in empty_metadata_t clone_e2e_meta) {
    @name("p") CommonParser() p_1;
    state start {
        {
            p_1.apply(buffer, parsed_hdr, user_meta);
        }
        transition accept;
    }
}
control ingress(inout headers hdr, inout metadata user_meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
    @name("port_bytes_in") Counter<ByteCounter_t, PortId_t>(32w512, PSA_CounterType_t.BYTES) port_bytes_in_0;
    @name("per_prefix_pkt_byte_count") DirectCounter<PacketByteCounter_t>(PSA_CounterType_t.PACKETS_AND_BYTES) per_prefix_pkt_byte_count_0;
    @name("next_hop") action next_hop_0(PortId_t oport) {
        {
            per_prefix_pkt_byte_count_0.count();
        }
        {
            send_to_port(ostd, oport);
        }
    }
    @name("default_route_drop") action default_route_drop_0() {
        {
            per_prefix_pkt_byte_count_0.count();
        }
        {
            ingress_drop(ostd);
        }
    }
    @name("ipv4_da_lpm") table ipv4_da_lpm_0 {
        key = {
            hdr.ipv4.dstAddr: lpm @name("hdr.ipv4.dstAddr") ;
        }
        actions = {
            next_hop_0();
            default_route_drop_0();
        }
        default_action = default_route_drop_0();
        psa_direct_counter = per_prefix_pkt_byte_count_0;
    }
    apply {
        {
            port_bytes_in_0.count(istd.ingress_port);
        }
        if (hdr.ipv4.isValid()) {
            ipv4_da_lpm_0.apply();
        }
    }
}
control egress(inout headers hdr, inout metadata user_meta, in psa_egress_input_metadata_t istd, inout psa_egress_output_metadata_t ostd) {
    @name("port_bytes_out") Counter<ByteCounter_t, PortId_t>(32w512, PSA_CounterType_t.BYTES) port_bytes_out_0;
    apply {
        {
            port_bytes_out_0.count(istd.egress_port);
        }
    }
}
control CommonDeparserImpl(packet_out packet, inout headers hdr) {
    apply {
        {
            packet.emit<ethernet_t>(hdr.ethernet);
        }
        {
            packet.emit<ipv4_t>(hdr.ipv4);
        }
    }
}
control IngressDeparserImpl(packet_out buffer, out empty_metadata_t clone_i2e_meta, out empty_metadata_t resubmit_meta, out empty_metadata_t normal_meta, inout headers hdr, in metadata meta, in psa_ingress_output_metadata_t istd) {
    @name("cp") CommonDeparserImpl() cp_0;
    apply {
        {
            cp_0.apply(buffer, hdr);
        }
    }
}
control EgressDeparserImpl(packet_out buffer, out empty_metadata_t clone_e2e_meta, out empty_metadata_t recirculate_meta, inout headers hdr, in metadata meta, in psa_egress_output_metadata_t istd, in psa_egress_deparser_input_metadata_t edstd) {
    @name("cp") CommonDeparserImpl() cp_1;
    apply {
        {
            cp_1.apply(buffer, hdr);
        }
    }
}
IngressPipeline<headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(IngressParserImpl(), ingress(), IngressDeparserImpl()) ip;
EgressPipeline<headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(EgressParserImpl(), egress(), EgressDeparserImpl()) ep;
PSA_Switch<headers, metadata, headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;
