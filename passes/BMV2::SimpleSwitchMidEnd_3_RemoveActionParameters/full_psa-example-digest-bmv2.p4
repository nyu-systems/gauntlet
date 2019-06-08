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
struct headers {
    ethernet_t ethernet;
    ipv4_t     ipv4;
    bit<16>    type;
}
struct empty_metadata_t {
}
struct mac_learn_digest_t {
    EthernetAddress srcAddr;
    PortId_t        ingress_port;
}
struct metadata {
    bool               send_mac_learn_msg;
    mac_learn_digest_t mac_learn_msg;
}
parser IngressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata meta, in psa_ingress_parser_input_metadata_t istd, in empty_metadata_t resubmit_meta, in empty_metadata_t recirculate_meta) {
    headers parsed_hdr_2;
    metadata meta_0;
    state start {
        parsed_hdr_2.ethernet.setInvalid();
        parsed_hdr_2.ipv4.setInvalid();
        meta_0 = meta;
        transition CommonParser_start;
    }
    state CommonParser_start {
        buffer.extract<ethernet_t>(parsed_hdr_2.ethernet);
        transition select(parsed_hdr_2.ethernet.etherType) {
            16w0x800: CommonParser_parse_ipv4;
            default: start_0;
        }
    }
    state CommonParser_parse_ipv4 {
        buffer.extract<ipv4_t>(parsed_hdr_2.ipv4);
        transition start_0;
    }
    state start_0 {
        parsed_hdr = parsed_hdr_2;
        meta = meta_0;
        transition accept;
    }
}
parser EgressParserImpl(packet_in buffer, out headers parsed_hdr, inout metadata meta, in psa_egress_parser_input_metadata_t istd, in empty_metadata_t normal_meta, in empty_metadata_t clone_i2e_meta, in empty_metadata_t clone_e2e_meta) {
    headers parsed_hdr_3;
    metadata meta_5;
    state start {
        parsed_hdr_3.ethernet.setInvalid();
        parsed_hdr_3.ipv4.setInvalid();
        meta_5 = meta;
        transition CommonParser_start_0;
    }
    state CommonParser_start_0 {
        buffer.extract<ethernet_t>(parsed_hdr_3.ethernet);
        transition select(parsed_hdr_3.ethernet.etherType) {
            16w0x800: CommonParser_parse_ipv4_0;
            default: start_1;
        }
    }
    state CommonParser_parse_ipv4_0 {
        buffer.extract<ipv4_t>(parsed_hdr_3.ipv4);
        transition start_1;
    }
    state start_1 {
        parsed_hdr = parsed_hdr_3;
        meta = meta_5;
        transition accept;
    }
}
control ingress(inout headers hdr, inout metadata meta, in psa_ingress_input_metadata_t istd, inout psa_ingress_output_metadata_t ostd) {
    psa_ingress_output_metadata_t meta_6;
    PortId_t egress_port_0;
    psa_ingress_output_metadata_t meta_7;
    PortId_t egress_port_3;
    @name(".NoAction") action NoAction_0() {
    }
    @name(".NoAction") action NoAction_4() {
    }
    @name(".NoAction") action NoAction_5() {
    }
    @name("ingress.unknown_source") action unknown_source_0() {
        meta.send_mac_learn_msg = true;
        meta.mac_learn_msg.srcAddr = hdr.ethernet.srcAddr;
        meta.mac_learn_msg.ingress_port = istd.ingress_port;
    }
    @name("ingress.learned_sources") table learned_sources {
        key = {
            hdr.ethernet.srcAddr: exact @name("hdr.ethernet.srcAddr") ;
        }
        actions = {
            NoAction_0();
            unknown_source_0();
        }
        default_action = unknown_source_0();
    }
    @name("ingress.do_L2_forward") action do_L2_forward_0(PortId_t egress_port) {
        {
            meta_6 = ostd;
            egress_port_0 = egress_port;
            meta_6.drop = false;
            meta_6.multicast_group = 10w0;
            meta_6.egress_port = egress_port_0;
            ostd = meta_6;
        }
    }
    @name("ingress.do_tst") action do_tst_0(PortId_t egress_port, bit<16> serEnumT) {
        {
            meta_7 = ostd;
            egress_port_3 = egress_port;
            meta_7.drop = false;
            meta_7.multicast_group = 10w0;
            meta_7.egress_port = egress_port_3;
            ostd = meta_7;
        }
    }
    @name("ingress.l2_tbl") table l2_tbl {
        key = {
            hdr.ethernet.dstAddr: exact @name("hdr.ethernet.dstAddr") ;
        }
        actions = {
            do_L2_forward_0();
            NoAction_4();
        }
        default_action = NoAction_4();
    }
    @name("ingress.tst_tbl") table tst_tbl {
        key = {
            meta.mac_learn_msg.ingress_port: exact @name("meta.mac_learn_msg.ingress_port") ;
        }
        actions = {
            do_tst_0();
            NoAction_5();
        }
        default_action = NoAction_5();
    }
    apply {
        meta.send_mac_learn_msg = false;
        learned_sources.apply();
        l2_tbl.apply();
        tst_tbl.apply();
    }
}
control egress(inout headers hdr, inout metadata meta, in psa_egress_input_metadata_t istd, inout psa_egress_output_metadata_t ostd) {
    apply {
    }
}
control IngressDeparserImpl(packet_out packet, out empty_metadata_t clone_i2e_meta, out empty_metadata_t resubmit_meta, out empty_metadata_t normal_meta, inout headers hdr, in metadata meta, in psa_ingress_output_metadata_t istd) {
    @name("IngressDeparserImpl.mac_learn_digest") Digest<mac_learn_digest_t>() mac_learn_digest;
    apply {
        if (meta.send_mac_learn_msg) 
            mac_learn_digest.pack(meta.mac_learn_msg);
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<ipv4_t>(hdr.ipv4);
    }
}
control EgressDeparserImpl(packet_out packet, out empty_metadata_t clone_e2e_meta, out empty_metadata_t recirculate_meta, inout headers hdr, in metadata meta, in psa_egress_output_metadata_t istd, in psa_egress_deparser_input_metadata_t edstd) {
    apply {
        packet.emit<ethernet_t>(hdr.ethernet);
        packet.emit<ipv4_t>(hdr.ipv4);
    }
}
IngressPipeline<headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(IngressParserImpl(), ingress(), IngressDeparserImpl()) ip;
EgressPipeline<headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(EgressParserImpl(), egress(), EgressDeparserImpl()) ep;
PSA_Switch<headers, metadata, headers, metadata, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t, empty_metadata_t>(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;
