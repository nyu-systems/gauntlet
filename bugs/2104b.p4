#include <core.p4>
#include <v1model.p4>

// adding the inout qualifier leads to a compiler crash
bit<8> test(inout bit<8> x) {
    return x;
}

header H {
    bit<8> a;
    bit<8> b;
}

struct headers {
    H h;
}

control c(inout headers hdr) {
    apply {
        test(hdr.h.a);
    }
}

control e<T>(inout T t);
package top<T>(e<T> e);

top(c()) main;
