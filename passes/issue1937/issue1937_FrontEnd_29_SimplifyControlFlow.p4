#include <core.p4>
header h1_t {
    bit<8> f1;
    bit<8> f2;
}
parser foo(out bit<8> x, in bit<8> y=5) {
    state start {
        x = y >> 2;
        transition accept;
    }
}
parser parserImpl(out h1_t hdr) {
    @name("foo") foo() foo_inst_1;
    @name("foo") foo() foo_inst_2;
    bit<8> tmp;
    bit<8> tmp_0;
    state start {
        tmp_0 = hdr.f1;
        foo_inst_1.apply(tmp, tmp_0);
        hdr.f1 = tmp;
        foo_inst_2.apply(x = hdr.f2, y = 8w5);
        transition accept;
    }
}
parser p<T>(out T h);
package top<T>(p<T> p);
top<h1_t>(parserImpl()) main;
