#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header lzMhAp {
    bit<64>  AXIR;
    bit<128> ahNS;
    bit<8>   TJnK;
    bit<32>  BXEC;
    bit<8>   svFH;
}

header AVFudW {
    bit<128> YfEi;
}

struct urUmmZ {
    ethernet_t rhvf;
}

struct cephAh {
    ethernet_t HlnN;
}

struct Headers {
    ethernet_t eth_hdr;
    ethernet_t UCJA;
    lzMhAp     GebN;
    lzMhAp     PaPw;
    lzMhAp     KSLP;
    lzMhAp     Rsnp;
}

struct Meta {
}

bit<4> jgIRKLG(in bit<128> JXFA, out bit<64> Eqiy) {
    Eqiy = (bit<64>)(((JXFA ^ (bit<128>)(0))));
    bit<8> zEUXIn = 8w3;
    zEUXIn = (bit<8>)(((Eqiy << (bit<8>)(1w0))));
    return (bit<4>)((((JXFA <= 4) ? (Eqiy << (bit<8>)(1w0)) : (bit<64>)(4w4))));
}
parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    bit<64> ERMHQg = 64w0;
    bit<16> czaRJI = 16w2;
    ethernet_t lScDCr = { 0, 48w3, 0 };
    bit<16> UMcQkF = 16w2;
    urUmmZ dqqjok = { { 2, 48w1, 16w0 } };
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.UCJA);
        pkt.extract(hdr.GebN);
        pkt.extract(hdr.PaPw);
        pkt.extract(hdr.KSLP);
        pkt.extract(hdr.Rsnp);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    bit<64> grncDr = 64w0;
    action bdGgT(out bit<8> PjJk) {
        bit<8> QWeQQr = 8w2;
        {
            ethernet_t FyVSYV = { 2, 48w0, 16w1 };
            urUmmZ cMsySI = { { 0, 48w3, 16w1 } };
            return;
            jgIRKLG(h.KSLP.ahNS, grncDr);
            return;
        }
        QWeQQr = (bit<8>)(((3 % 4w1)));
        bit<128> ZrTICG = 128w3;
        jgIRKLG(ZrTICG, grncDr);
        QWeQQr = (bit<8>)((~((3 % 4w1))));
        PjJk = (bit<8>)((((~((3 % 4w1))) >> (bit<8>)(jgIRKLG(ZrTICG, grncDr)))));
        jgIRKLG(ZrTICG, grncDr);
    }
    action ULQUr(inout bit<16> GKqh, out bit<16> hvvv, out bit<8> CcYq) {
        bdGgT(CcYq);
        urUmmZ TjRatp = { { 48w1, 1, 0 } };
        jgIRKLG(h.GebN.ahNS, grncDr);
        bit<32> JBKuqW = 32w0;
        JBKuqW = (bit<32>)(((3 |+| (bit<4>)(1w0))));
        bit<32> yoDjRN = 32w0;
    }
    table bPsGUq {
        key = {
            grncDr: exact @name("EozywC") ;
            grncDr: exact @name("UtFZUH") ;
        }
        actions = {
            bdGgT(h.KSLP.svFH);
        }
    }
    apply {
        bPsGUq.apply();
        jgIRKLG(h.PaPw.ahNS, grncDr);
        {
            bdGgT(h.GebN.svFH);
            bit<64> bmkbZf = 64w1;
            bmkbZf = (bit<64>)(((3w3 * (bit<3>)(2w1))));
            exit;
            grncDr = (bit<64>)(((jgIRKLG(h.Rsnp.ahNS, grncDr) & (bit<4>)(0))));
            bit<8> PKrOsu = 8w2;
        }
        jgIRKLG(h.Rsnp.ahNS, grncDr);
        bit<8> jRJhEK = 8w1;
    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {b.emit(h);} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

