extern bit<32> f(in bit<32> x);
header H {
    bit<32> v;
}
control c(inout bit<32> r) {
    H[2] h_0;
    bit<32> tmp;
    apply {
        tmp = f(32w2);
        h_0[tmp].setValid();
    }
}
control simple(inout bit<32> r);
package top(simple e);
top(c()) main;
