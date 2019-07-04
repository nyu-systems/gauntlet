struct PortId_t {
    bit<9> _v;
}
header H {
    bit<32> b;
}
struct metadata_t {
    PortId_t foo;
}
control I(inout metadata_t meta) {
    H h_0;
    apply {
        h_0.setValid();
        if (true && meta.foo._v == 9w192) {
            meta.foo._v = meta.foo._v + 9w1;
            h_0.setValid();
            {
                h_0.b = 32w2;
            }
            if (!h_0.isValid() && !true || h_0.isValid() && true && h_0.b == 32w1) 
                h_0.setValid();
        }
    }
}
control C<M>(inout M m);
package top<M>(C<M> c);
top<metadata_t>(I()) main;
