#include <core.p4>
#include <v1model.p4>

header ocbqXF {
    bit<64>  BqDd;
    bit<128> tiiq;
}

header_union PHPFGx {
    ocbqXF jPoM;
}

struct KJfxfG {
    bit<16> LzlP;
}

struct tUoWwm {
    bit<32> mTxK;
    ocbqXF  EctP;
    PHPFGx  oRii;
}

struct TsJmpC {
    PHPFGx    eZfQ;
    PHPFGx[4] MOcW;
    bit<32>   xsSj;
    bit<32>   CQGM;
}

struct Headers {
    PHPFGx[5] PAEV;
    PHPFGx[5] Sdag;
    PHPFGx[6] zyZt;
    ocbqXF    LYTt;
    ocbqXF    vhAm;
}

struct Meta {
    ocbqXF[1] WcVw;
    PHPFGx[1] lKwk;
    ocbqXF    FVhd;
    bit<8>    NvVW;
    bit<32>   Drqv;
}

control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
    action ygRAs() {
        if (sm.enq_timestamp != 6) {
            sm = sm;
        }
    }

    apply {
        sm.egress_spec = 2;
        ygRAs();

    }
}

parser p(packet_in b, out Headers h, inout Meta m, inout standard_metadata_t sm) {
state start {transition accept;}}

control vrfy(inout Headers h, inout Meta m) { apply {} }

control update(inout Headers h, inout Meta m) { apply {} }

control egress(inout Headers h, inout Meta m, inout standard_metadata_t sm) { apply {} }

control deparser(packet_out b, in Headers h) { apply {} }

V1Switch(p(), vrfy(), ingress(), egress(), update(), deparser()) main;

