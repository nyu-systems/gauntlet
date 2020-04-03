#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header KFHwlQ {
    bit<16> aHHG;
    bit<16> NNfm;
}

header sJKnzl {
    bit<8>   Etxp;
    bit<128> vyjJ;
    bit<16>  nqKa;
    bit<16>  oAoE;
    bit<8>   VgTN;
}

struct kzlNHB {
    ethernet_t tbBw;
    bit<128>   aorq;
    bit<128>   Bzmg;
}

struct ivSVft {
    bit<32> sAIX;
}

struct Headers {
    ethernet_t eth_hdr;
    sJKnzl     KsVa;
}

struct Meta {
}

bit<16> WeDYdSg(in bit<64> MIIj, out bit<64> voGw) {
    return 16w4;
}
bit<16> kGbzUus(inout bit<16> IZOt, in bit<8> qYHN, out bit<64> JeiW) {
    return WeDYdSg(64w6, JeiW);;
}
parser p(packet_in pkt, out Headers hdr, inout Meta m, inout standard_metadata_t sm) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        transition accept;
    }
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    kzlNHB fJbcCy = { { (bit<48>)(h.eth_hdr.dst_addr), 48w3, 16w2 }, (((false ? (bit<128>)((bit<128>)(h.KsVa.Etxp)) : (bit<128>)(128w3))) |-| (bit<128>)(h.eth_hdr.eth_type)), (128w4 ^ (128w1 + 128w5)) };
    sJKnzl WhpQNS = { 8w5, (((bit<130>)(130w4))[128:1]), 16w6, (16w3 - (((!(!(((!((94w2 != 94w5))) || (!false))))) ? (bit<16>)(16w5) : (bit<16>)((bit<16>)(fJbcCy.Bzmg))))), 8w4 };
    action SyQJb() {
        ivSVft uWGboh = { 32w4 };
        {
            bit<64> wbCvtq = (((!(!(!(!true)))) ? (bit<64>)((bit<64>)(uWGboh.sAIX)) : (bit<64>)(64w3)));
            WeDYdSg(64w5, wbCvtq);
        }
        {
            bit<64> shXKCL = 64w2;
            kGbzUus(h.KsVa.oAoE, (bit<8>)(WhpQNS.oAoE), shXKCL);
        }
        return;
    }

    table ljZldB {
        key = {
        }
        actions = {
            SyQJb();
        }
    }
    apply {
        {
            bit<64> iIJoaq = (64w3 + ((64w6 | 64w6)));
            WeDYdSg(((bit<64>)(iIJoaq) + (bit<64>)(WeDYdSg((bit<64>)(WhpQNS.Etxp), iIJoaq))), iIJoaq);
        }
        switch (ljZldB.apply().action_run) {
            SyQJb: {
            }
        }

    }
}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {b.emit(h);} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

