#include <core.p4>
header hdr {
    bit<32> a;
    bit<32> b;
    bit<8>  c;
}
control ingress(inout hdr h) {
    apply {
        h.a = h.a & ~32w0xff | (bit<32>)((bit<32>)h.c)[7:0] << 0 & 32w0xff;
        h.a = h.a & ~32w0xff00 | (bit<32>)(h.c + h.c)[7:0] << 8 & 32w0xff00;
    }
}
control c(inout hdr h);
package top(c _c);
top(ingress()) main;
