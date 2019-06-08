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
    Ethernet e;
    state start {
        p.extract<Ethernet>(e);
        transition select(e.type) {
            16w0x800: accept;
            16w0x806: accept;
            default: reject;
        }
    }
}
control c(inout Headers h) {
    bool hasReturned_0;
    apply {
        hasReturned_0 = false;
        if (!h.eth.isValid()) 
            hasReturned_0 = true;
        if (!hasReturned_0) 
            if (h.eth.type == 16w0x800) 
                h.eth.setInvalid();
            else 
                h.eth.type = 16w0;
    }
}
parser p<H>(packet_in _p, out H h);
control ctr<H>(inout H h);
package top<H>(p<H> _p, ctr<H> _c);
top<Headers>(prs(), c()) main;
