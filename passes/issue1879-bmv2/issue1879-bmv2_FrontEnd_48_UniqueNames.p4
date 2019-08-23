#include <core.p4>
#include <v1model.p4>
header preamble_t {
    bit<336> data;
}
header prot_common_t {
    bit<4>  version;
    bit<6>  dstType;
    bit<6>  srcType;
    bit<16> totalLen;
    bit<8>  hdrLen;
    bit<8>  curri;
    bit<8>  currh;
    bit<8>  nextHdr;
}
header prot_addr_common_t {
    bit<128> data;
}
header prot_host_addr_ipv4_t {
    bit<32> addr;
}
header_union prot_host_addr_t {
    prot_host_addr_ipv4_t ipv4;
}
header prot_host_addr_padding_t {
    varbit<32> padding;
}
header prot_i_t {
    bit<7>  data;
    bit<1>  upDirection;
    bit<48> data2;
    bit<8>  segLen;
}
header prot_h_t {
    bit<64> data;
}
struct currenti_t {
    bit<1> upDirection;
}
struct metadata {
    bit<8>     headerLen;
    bit<8>     hLeft;
    bit<9>     addrLen;
    bit<8>     currPos;
    currenti_t currenti;
}
struct headers {
    preamble_t               preamble;
    prot_common_t            prot_common;
    prot_addr_common_t       prot_addr_common;
    prot_host_addr_t         prot_host_addr_dst;
    prot_host_addr_t         prot_host_addr_src;
    prot_host_addr_padding_t prot_host_addr_padding;
    prot_i_t                 prot_inf_0;
    prot_h_t[10]             prot_h_0;
    prot_i_t                 prot_inf_1;
}
parser PROTParser(packet_in packet, out headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    bit<9> paddingLen;
    bool currentISelected;
    bit<8> hdrLeft;
    bool currentISelected_3;
    prot_i_t inf;
    metadata meta_1;
    bool currentISelected_4;
    bit<8> currI;
    bool subParser_currentISelected2_0;
    state start {
        packet.extract<preamble_t>(hdr.preamble);
        packet.extract<prot_common_t>(hdr.prot_common);
        packet.extract<prot_addr_common_t>(hdr.prot_addr_common);
        meta.headerLen = hdr.prot_common.hdrLen;
        packet.extract<prot_host_addr_ipv4_t>(hdr.prot_host_addr_dst.ipv4);
        meta.addrLen = 9w32;
        transition select(hdr.prot_common.srcType) {
            6w0x1: parse_prot_host_addr_src_ipv4;
        }
    }
    state parse_prot_host_addr_src_ipv4 {
        packet.extract<prot_host_addr_ipv4_t>(hdr.prot_host_addr_src.ipv4);
        meta.addrLen = meta.addrLen + 9w32;
        paddingLen = 9w64 - (meta.addrLen & 9w63) & 9w63;
        packet.extract<prot_host_addr_padding_t>(hdr.prot_host_addr_padding, (bit<32>)paddingLen);
        meta.addrLen = meta.addrLen + paddingLen;
        meta.currPos = (bit<8>)(9w3 + (meta.addrLen >> 6));
        currentISelected = hdr.prot_common.curri == meta.currPos;
        inf.setInvalid();
        meta_1 = meta;
        currentISelected_4 = currentISelected;
        currI = hdr.prot_common.curri;
        transition SubParser_start;
    }
    state SubParser_start {
        packet.extract<prot_i_t>(inf);
        subParser_currentISelected2_0 = currI == meta_1.currPos;
        meta_1.currenti.upDirection = meta_1.currenti.upDirection + (bit<1>)subParser_currentISelected2_0 * inf.upDirection;
        meta_1.hLeft = inf.segLen;
        meta_1.currPos = meta_1.currPos + 8w1;
        transition parse_prot_host_addr_src_ipv4_0;
    }
    state parse_prot_host_addr_src_ipv4_0 {
        hdr.prot_inf_0 = inf;
        meta = meta_1;
        transition parse_prot_h_0_pre;
    }
    state parse_prot_h_0_pre {
        transition select(meta.hLeft) {
            8w0: parse_prot_1;
            default: parse_prot_h_0;
        }
    }
    state parse_prot_h_0 {
        packet.extract<prot_h_t>(hdr.prot_h_0.next);
        meta.hLeft = meta.hLeft + 8w255;
        meta.currPos = meta.currPos + 8w1;
        transition parse_prot_h_0_pre;
    }
    state parse_prot_1 {
        hdrLeft = meta.headerLen - meta.currPos;
        transition select(hdrLeft) {
            8w0: accept;
            default: parse_prot_inf_1;
        }
    }
    state parse_prot_inf_1 {
        currentISelected_3 = meta.currPos == hdr.prot_common.curri;
        inf.setInvalid();
        meta_1 = meta;
        currentISelected_4 = currentISelected_3;
        currI = hdr.prot_common.curri;
        transition SubParser_start_0;
    }
    state SubParser_start_0 {
        packet.extract<prot_i_t>(inf);
        subParser_currentISelected2_0 = currI == meta_1.currPos;
        meta_1.currenti.upDirection = meta_1.currenti.upDirection + (bit<1>)subParser_currentISelected2_0 * inf.upDirection;
        meta_1.hLeft = inf.segLen;
        meta_1.currPos = meta_1.currPos + 8w1;
        transition parse_prot_inf;
    }
    state parse_prot_inf {
        hdr.prot_inf_1 = inf;
        meta = meta_1;
        transition accept;
    }
}
control PROTVerifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control PROTIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
        if (meta.currenti.upDirection == 1w0) {
            mark_to_drop(standard_metadata);
        }
    }
}
control PROTEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
    apply {
    }
}
control PROTComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}
control PROTDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit<headers>(hdr);
    }
}
V1Switch<headers, metadata>(PROTParser(), PROTVerifyChecksum(), PROTIngress(), PROTEgress(), PROTComputeChecksum(), PROTDeparser()) main;
