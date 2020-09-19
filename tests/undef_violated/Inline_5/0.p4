error {
    NoError,
    PacketTooShort,
    NoMatch,
    StackOutOfBounds,
    HeaderTooShort,
    ParserTimeout,
    ParserInvalidArgument,
    CounterRange,
    Timeout,
    PhvOwner,
    MultiWrite,
    IbufOverflow,
    IbufUnderflow
}

extern packet_in {
    void extract<T>(out T hdr);
    void extract<T>(out T variableSizeHeader, in bit<32> variableFieldSizeInBits);
    T lookahead<T>();
    void advance(in bit<32> sizeInBits);
    bit<32> length();
}

extern packet_out {
    void emit<T>(in T hdr);
}

extern void verify(in bool check, in error toSignal);
match_kind {
    exact,
    ternary,
    lpm
}

match_kind {
    range,
    selector,
    atcam_partition_index
}

@__intrinsic_metadata header ingress_intrinsic_metadata_t {
}

@__intrinsic_metadata struct ingress_intrinsic_metadata_for_tm_t {
}

@__intrinsic_metadata struct ingress_intrinsic_metadata_from_parser_t {
}

@__intrinsic_metadata struct ingress_intrinsic_metadata_for_deparser_t {
}

@__intrinsic_metadata header egress_intrinsic_metadata_t {
}

@__intrinsic_metadata struct egress_intrinsic_metadata_from_parser_t {
}

@__intrinsic_metadata struct egress_intrinsic_metadata_for_deparser_t {
}

@__intrinsic_metadata struct egress_intrinsic_metadata_for_output_port_t {
}

parser IngressParserT<H, M>(packet_in pkt, out H hdr, out M ig_md, @optional out ingress_intrinsic_metadata_t ig_intr_md, @optional out ingress_intrinsic_metadata_for_tm_t ig_intr_md_for_tm, @optional out ingress_intrinsic_metadata_from_parser_t ig_intr_md_from_prsr);
parser EgressParserT<H, M>(packet_in pkt, out H hdr, out M eg_md, @optional out egress_intrinsic_metadata_t eg_intr_md, @optional out egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr);
control IngressT<H, M>(inout H hdr, inout M ig_md, @optional in ingress_intrinsic_metadata_t ig_intr_md, @optional in ingress_intrinsic_metadata_from_parser_t ig_intr_md_from_prsr, @optional inout ingress_intrinsic_metadata_for_deparser_t ig_intr_md_for_dprsr, @optional inout ingress_intrinsic_metadata_for_tm_t ig_intr_md_for_tm);
control EgressT<H, M>(inout H hdr, inout M eg_md, @optional in egress_intrinsic_metadata_t eg_intr_md, @optional in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr, @optional inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr, @optional inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport);
control IngressDeparserT<H, M>(packet_out pkt, inout H hdr, in M metadata, @optional in ingress_intrinsic_metadata_for_deparser_t ig_intr_md_for_dprsr, @optional in ingress_intrinsic_metadata_t ig_intr_md);
control EgressDeparserT<H, M>(packet_out pkt, inout H hdr, in M metadata, @optional in egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr, @optional in egress_intrinsic_metadata_t eg_intr_md, @optional in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr);
package Pipeline<IH, IM, EH, EM>(IngressParserT<IH, IM> ingress_parser, IngressT<IH, IM> ingress, IngressDeparserT<IH, IM> ingress_deparser, EgressParserT<EH, EM> egress_parser, EgressT<EH, EM> egress, EgressDeparserT<EH, EM> egress_deparser);
@pkginfo(arch="TNA", version="1.0.1") package Switch<IH0, IM0, EH0, EM0, IH1, IM1, EH1, EM1, IH2, IM2, EH2, EM2, IH3, IM3, EH3, EM3>(Pipeline<IH0, IM0, EH0, EM0> pipe0, @optional Pipeline<IH1, IM1, EH1, EM1> pipe1, @optional Pipeline<IH2, IM2, EH2, EM2> pipe2, @optional Pipeline<IH3, IM3, EH3, EM3> pipe3);
header ethernet_h {
    bit<32> dst_addr;
    bit<32> src_addr;
    bit<16> eth_type;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

struct header_t {
    ethernet_h eth_hdr;
}

parser SwitchIngressParser(packet_in pkt, out header_t hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        transition accept;
    }
}

control SwitchIngressDeparser(packet_out pkt, inout header_t hdr, in ingress_metadata_t ig_md, in ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md) {
    apply {
    }
}

parser SwitchEgressParser(packet_in pkt, out header_t hdr, out egress_metadata_t eg_md, out egress_intrinsic_metadata_t eg_intr_md) {
    state start {
        transition accept;
    }
}

control SwitchEgressDeparser(packet_out pkt, inout header_t hdr, in egress_metadata_t eg_md, in egress_intrinsic_metadata_for_deparser_t eg_dprsr_md) {
    apply {
    }
}

control SwitchIngress(inout header_t hdr, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bit<8> undef_0;
    apply {
        if (undef_0 == 8w1) {
            undef_0 = 8w1;
        }
        {
            if (undef_0 == 8w1) {
                hdr.eth_hdr.eth_type = 16w1;
            }
        }
    }
}

control SwitchEgress(inout header_t hdr, inout egress_metadata_t eg_md, in egress_intrinsic_metadata_t eg_intr_md, in egress_intrinsic_metadata_from_parser_t eg_intr_from_prsr, inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr, inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport) {
    apply {
    }
}

Pipeline<header_t, ingress_metadata_t, header_t, egress_metadata_t>(SwitchIngressParser(), SwitchIngress(), SwitchIngressDeparser(), SwitchEgressParser(), SwitchEgress(), SwitchEgressDeparser()) pipe;

Switch<header_t, ingress_metadata_t, header_t, egress_metadata_t, _, _, _, _, _, _, _, _, _, _, _, _>(pipe) main;

