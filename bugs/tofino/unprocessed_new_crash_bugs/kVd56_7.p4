#include <core.p4>
#define __TARGET_TOFINO__ 1
#include <tna.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header KwQsXl {
    bit<32> ECZS;
    bit<4>  Qbzc;
    bit<4>  padding;
}

struct Headers {
    ethernet_t eth_hdr;
    KwQsXl     IoEd;
    ethernet_t gAFK;
}

struct ingress_metadata_t {
}

struct egress_metadata_t {
}

action waRsX(bit<32> YZwq, bit<4> Zmgq) {
    bit<16> ELwpZn = (bit<16>)Zmgq;
    ELwpZn = -1946487849 * ELwpZn;
    ELwpZn = 16w27570;
    ELwpZn = 16w63565;
}
parser SwitchIngressParser(packet_in pkt, out Headers hdr, out ingress_metadata_t ig_md, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.IoEd);
        pkt.extract(hdr.gAFK);
        transition accept;
    }
}

control ingress(inout Headers h, inout ingress_metadata_t ig_md, in ingress_intrinsic_metadata_t ig_intr_md, in ingress_intrinsic_metadata_from_parser_t ig_prsr_md, inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md, inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    bit<64> CGpIvK = 64w7076467539859160835;
    bit<64> IEMnWf = (bit<64>)64w3827318462157963976 |+| 64w7117304322255855885 + 64w8123377691315302966 ^ CGpIvK | 1036943799;
    bool SFNFWW = 86w12801325154798814281711175 != ((bit<167>)167w26882383000565786188921522310857937713648794154109)[131:46];
    bool WRvrDg = !((bit<18>)h.eth_hdr.eth_type != (~(37w13958207214 | 37w93593291557))[26:9]);
    bit<4> lXzOXx = (bit<4>)1827086360 << 4w13;
    action USfIH() {
        h.eth_hdr.eth_type = -1011834326;
        h.IoEd.Qbzc = ((bit<91>)CGpIvK + 91w2379923011324881889882539421 != 91w1383924250324327884943409059 ? (bit<4>)4w15 : 4w0) + 4w11 - 4w8;
        h.eth_hdr.dst_addr = h.gAFK.src_addr;
        bit<8> gkuBHq = 8w44;
        bit<64> jwiCHK = 64w17608225600757467510;
        h.eth_hdr.src_addr = h.gAFK.dst_addr;
        gkuBHq = 381482098;
        CGpIvK = CGpIvK;
        h.eth_hdr.src_addr = (bit<48>)48w114970607091906 |-| ((bit<117>)CGpIvK)[82:35];
        h.gAFK.eth_type = 16w8004;
    }
    action wKbxx() {
        bool UvXjZl = WRvrDg;
        h.gAFK.src_addr = (SFNFWW ? h.gAFK.dst_addr : h.gAFK.dst_addr);
        h.IoEd.ECZS = -~h.IoEd.ECZS;
        h.IoEd.ECZS = h.IoEd.ECZS |-| 32w2356319505;
    }
    action UFIby(in bit<4> epNE, bit<4> XPPH, bit<4> NydD) {
        h.eth_hdr.src_addr[31:28] = 4w1;
        IEMnWf = 372022833 - -118271259;
        h.gAFK.src_addr = (bit<48>)h.gAFK.dst_addr |-| 48w49162672875013 - h.eth_hdr.src_addr;
        CGpIvK = ((bit<55>)h.IoEd.Qbzc != 55w10705872549073362 ^ (true ? 55w16149665890810888 + 55w19908915435152001 : 55w12267500658097499) ? 64w14490836212018094954 : 64w3772054959105728609);
        h.IoEd.ECZS = h.IoEd.ECZS;
        const bit<128> jCloIp = 225w3969557485069738260714101266151978385111713893769293306138249438885[159:32];
        return;
        bit<16> KCnpFh = (193w12381288832092583476226731325257279188267123328014326372927[181:15][114:53] << (bit<8>)62w4457069787350725239)[59:44];
    }
    table LuLHxC {
        key = {
            ((bit<77>)h.eth_hdr.eth_type)[63:32]                   : exact @name("rnUqHv") ;
            48w83542547241218 - 48w62144697243577 & h.gAFK.dst_addr: exact @name("oThEiv") ;
            64w9348650588642301266                                 : exact @name("gHoGag") ;
        }
        actions = {
            wKbxx();
            UFIby(1w1 ++ 3w1 & 4w6 |+| 4w3);
            waRsX();
        }
    }
    apply {
        ig_tm_md.ucast_egress_port = 0;
        wKbxx();
        CGpIvK = IEMnWf;
        h.IoEd.Qbzc = 4w3;
        h.eth_hdr.eth_type = h.eth_hdr.eth_type;
        h.IoEd.Qbzc = 4w15;
        CGpIvK = 64w12805727972945614624 |+| 64w18134960303949310388;
    }
}

control SwitchIngressDeparser(packet_out pkt, inout Headers h, in ingress_metadata_t ig_md, in ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md) {
    apply {
        pkt.emit(h);
    }
}

parser SwitchEgressParser(packet_in pkt, out Headers h, out egress_metadata_t eg_md, out egress_intrinsic_metadata_t eg_intr_md) {
    state start {
        pkt.extract(eg_intr_md);
        transition accept;
    }
}

control SwitchEgress(inout Headers h, inout egress_metadata_t eg_md, in egress_intrinsic_metadata_t eg_intr_md, in egress_intrinsic_metadata_from_parser_t eg_intr_md_from_prsr, inout egress_intrinsic_metadata_for_deparser_t eg_intr_dprs_md, inout egress_intrinsic_metadata_for_output_port_t eg_intr_oport_md) {
    apply {
    }
}

control SwitchEgressDeparser(packet_out pkt, inout Headers h, in egress_metadata_t eg_md, in egress_intrinsic_metadata_for_deparser_t eg_intr_dprs_md) {
    apply {
        pkt.emit(h);
    }
}

Pipeline(SwitchIngressParser(), ingress(), SwitchIngressDeparser(), SwitchEgressParser(), SwitchEgress(), SwitchEgressDeparser()) pipe;

Switch(pipe) main;

