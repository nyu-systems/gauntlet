#include <core.p4>
header Ethernet {
    bit<48> src;
    bit<48> dest;
    bit<16> type;
}
struct Headers {
    Ethernet eth;
}
parser prs(packet_in p, out Headers h) {
    Ethernet e_0;
    state start {
        p.extract<Ethernet>(e_0);
        transition select(e_0.type) {
            16w0x800: accept;
            16w0x806: accept;
            default: reject;
        }
    }
}
control c(inout Headers h) {
    apply {
        bool hasReturned = false;
        if (!h.eth.isValid()) 
            hasReturned = true;
        if (!hasReturned) 
            if (h.eth.type == 16w0x800) 
                h.eth.setInvalid();
            else 
                h.eth.type = (bit<16>)16w0;
    }
}
parser p<H>(packet_in _p, out H h);
control ctr<H>(inout H h);
package top<H>(p<H> _p, ctr<H> _c);
top<Headers>(prs(), c()) main;
