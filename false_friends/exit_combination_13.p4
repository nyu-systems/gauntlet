#include <core.p4>
header ethernet_t {
    bit<48> dst_addr;
    bit<48> src_addr;
    bit<16> eth_type;
}

header Qiwjru {
    bit<16> LTfk;
    bit<64> UpsQ;
}

header xAtfsN {
    bit<8> vrxn;
}

struct Headers {
    ethernet_t eth_hdr;
    ethernet_t qAae;
    ethernet_t tjaP;
}

bool BOufial(in bool RytI, bool pMmY) {
    bool QoaAPP = !true;
    Qiwjru RmXodq = { (!(918049879 == 91w2125535317 | ((bit<166>)166w800678821)[96:6] && true) ? 16w28558 : 16w3284 - 16w12841), (bit<64>)832963967 |-| 64w870811214 };
    RmXodq.UpsQ = 64w1654657554;
    RmXodq.LTfk = 16w45804;
    RmXodq.UpsQ = 64w300892466;
    RmXodq.LTfk = 16w42468;
    RmXodq.LTfk = 4025;
    RmXodq.UpsQ = 64w2017016666;
    RmXodq.UpsQ = 64w489281572;
    RmXodq.LTfk = RmXodq.LTfk;
    if (!(3w0 / 3w7 == ((bit<45>)934573158)[32:30]) && true) {
        RmXodq.LTfk = 16w24623 & (!(!!(false && false) && !!true) ? 16w31382 : 16w56766 - 16w36946 |+| 16w8315);
    } else {
        RmXodq.LTfk = 7791;
    }
    return !RytI;
}
bool dJgrxtU(bit<32> SbLQ, bool xLMc, bit<64> SfeI) {
    const bit<64> QECnEe = 64w1930159719;
    bit<16> dpDvQr = 16w20540;
    dpDvQr = ((bit<90>)90w488317711)[34:19];
    dpDvQr = 16w35533 / 16w20979;
    dpDvQr = ~16w24745;
    dpDvQr = 16w32537;
    {
        {
            bool KpsIkS = false;
            BOufial(true, false || false && !false);
        }
        {
            bool Zemcae = !xLMc;
            BOufial(false, !false);
        }
        dpDvQr = 16w54432;
        dpDvQr = dpDvQr;
        dpDvQr = (!!xLMc ? dpDvQr : 16w63216);
        bool zEdvpm = !true;
        dpDvQr = 47624;
        BOufial(!zEdvpm, false && !!true);
        dpDvQr = dpDvQr;
        bool OoDKgr = BOufial(xLMc, false);
        dpDvQr = 16w54473;
        return !false;
    }
    dpDvQr = ((bit<89>)(bit<89>)SbLQ)[67:52];
    dpDvQr = 16w12429 / 16w50511;
    {
        bool DTjqjx = !true;
        BOufial(!false, !false);
    }
    return xLMc;
}
action ZFdiH(out bit<32> JObn, bit<16> LskT) {
    JObn = 32w328778690;
    JObn = JObn;
    JObn = 1724736818;
    JObn = (bit<32>)JObn >> (bit<8>)99w485356334[34:3];
    exit;
    const bool cwGPaq = false;
    const bool dyIkqH = true;
    if (false) {
        JObn = 32w1321104799;
    } else {
        JObn = 32w1105508437;
    }
}
parser p(packet_in pkt, out Headers hdr) {
    state start {
        transition parse_hdrs;
    }
    state parse_hdrs {
        pkt.extract(hdr.eth_hdr);
        pkt.extract(hdr.qAae);
        pkt.extract(hdr.tjaP);
        transition accept;
    }
}

control ingress(inout Headers h) {
    action simple_action() {
        exit;
    }
    table simple_table {
        key = {
            8w1   : exact @name("bblsPX") ;
        }
        actions = {
            simple_action();
        }
    }
    apply {
        switch (simple_table.apply().action_run) {
            simple_action: {
                h.eth_hdr.src_addr = 48w1;
            }
        }
        h.eth_hdr.dst_addr = 48w2;

    }
}

parser Parser(packet_in b, out Headers hdr);
control Ingress(inout Headers hdr);
package top(Parser p, Ingress ig);
top(p(), ingress()) main;

