#include <core.p4>
#include <pna.p4>

header Result { bit<48> dst; bit<48> src; bit<16> flags; }
header H { bit<8> x; }
header_union U { H a; H b; }
struct Headers { Result result; U u; }
struct Meta {}

parser P(packet_in packet, out Headers h, inout Meta m,
         in pna_main_parser_input_metadata_t istd) {
    state start {
        packet.extract(h.result);
        packet.extract(h.u.b);
        packet.extract(h.u.a);
        transition accept;
    }
}
control Pre(in Headers h, inout Meta m, in pna_pre_input_metadata_t istd,
            inout pna_pre_output_metadata_t ostd) { apply {} }
control I(inout Headers h, inout Meta m, in pna_main_input_metadata_t istd,
          inout pna_main_output_metadata_t ostd) {
    apply {
        h.result.flags = 0;
        if (h.u.a.isValid()) { h.result.flags = h.result.flags | 1; }
        if (h.u.b.isValid()) { h.result.flags = h.result.flags | 2; }
        send_to_port((PortId_t) 1);
    }
}
control D(packet_out packet, in Headers h, in Meta m,
          in pna_main_output_metadata_t ostd) {
    apply { packet.emit(h.result); }
}
PNA_NIC(P(), Pre(), I(), D()) main;
