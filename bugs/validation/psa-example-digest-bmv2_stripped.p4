#include <core.p4>
#include <psa.p4>

enum bit<16> dummy_enum {
    a = 0x0001,
    b = 0x0002
}
header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header H {
    bit<8> a;
    dummy_enum test;
}

struct Headers {
    ethernet_t eth_hdr;
    H h;
    dummy_enum test;
}

struct metadata {
}
struct empty_metadata_t {
}

parser sub_p(packet_in pkt, out Headers hdr) {
    state start {
        transition accept;
    }
}


parser IngressParserImpl(packet_in pkt, out Headers hdr, inout metadata meta,
                         in psa_ingress_parser_input_metadata_t istd,
                         in empty_metadata_t resubmit_meta,
                         in empty_metadata_t recirculate_meta) {
    sub_p() sub_parser;
    state start {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.h);
        sub_parser.apply(pkt, hdr);
        transition accept;
    }
}
parser EgressParserImpl(packet_in buffer,
                        out Headers parsed_hdr,
                        inout metadata meta,
                        in psa_egress_parser_input_metadata_t istd,
                        in empty_metadata_t normal_meta,
                        in empty_metadata_t clone_i2e_meta,
                        in empty_metadata_t clone_e2e_meta)
{

    state start {
        transition accept;
    }

}


control ingress(inout Headers hdr,
                inout metadata meta,
                in    psa_ingress_input_metadata_t  istd,
                inout psa_ingress_output_metadata_t ostd) {

    apply {
    }
}

control egress(inout Headers hdr,
               inout metadata meta,
               in    psa_egress_input_metadata_t  istd,
               inout psa_egress_output_metadata_t ostd)
{
    apply {
    }
}

control CommonDeparserImpl(packet_out packet,
                           inout Headers hdr)
{
    apply {
        packet.emit(hdr.eth_hdr);
        packet.emit(hdr.h);
    }
}

control IngressDeparserImpl(packet_out packet,
                            out empty_metadata_t clone_i2e_meta,
                            out empty_metadata_t resubmit_meta,
                            out empty_metadata_t normal_meta,
                            inout Headers hdr,
                            in metadata meta,
                            in psa_ingress_output_metadata_t istd)
{
    apply {
    }
}

control EgressDeparserImpl(packet_out packet,
                           out empty_metadata_t clone_e2e_meta,
                           out empty_metadata_t recirculate_meta,
                           inout Headers hdr,
                           in metadata meta,
                           in psa_egress_output_metadata_t istd,
                           in psa_egress_deparser_input_metadata_t edstd)
{
    apply {
    }
}

IngressPipeline(IngressParserImpl(),
                ingress(),
                IngressDeparserImpl()) ip;

EgressPipeline(EgressParserImpl(),
               egress(),
               EgressDeparserImpl()) ep;

PSA_Switch(ip, PacketReplicationEngine(), ep, BufferingQueueingEngine()) main;


